#include "Interpreter.h"

#include "core/Criterion.h"
#include "core/Util.h"
#include "preprocessing/ExplicitAssignPass.h"
#include "preprocessing/MarkAnalysisPass.h"

#include "llvm/IR/Argument.h"
#include "llvm/IR/User.h"

#include <cassert>
#include <iostream>

#define EXECUTE_INST_1(INST_NAME) \
	pNewTraceEntry = &execute##INST_NAME(*dyn_cast<INST_NAME const>(_pNextInst));

#define EXECUTE_INST_2(OP_CODE, INST_NAME) \
	case Instruction::OP_CODE: EXECUTE_INST_1(INST_NAME) break;

#define EXECUTE_BIN_OP(OP_CODE, OP) \
	case Instruction::OP_CODE: return updateState(inst, new DynInteger(OP));

#define EXECUTE_ICMP_INST(OP_CODE, OP_FUN) \
	case CmpInst::OP_CODE: return updateState(inst, new DynInteger(op1.OP_FUN(op2)));

#define EXECUTE_CAST_INST_BIT_WIDTH(OP_CODE, OP_FUN) \
	case CmpInst::OP_CODE: return updateState(inst, new DynInteger(value.OP_FUN(inst.getDestTy()->getIntegerBitWidth())));

using namespace std;
using namespace llvm;

static APInt undefValueAPInt;

Interpreter::Interpreter(
		Function     const& func,
		InputType    const& input,
		Heap&               heap,
		bool         const  branchDependencies,
		raw_ostream* const  pOut) :
	Interpreter(func, input, heap, branchDependencies, pOut, "") {}

Interpreter::Interpreter(
		Function     const& func,
		InputType    const& input,
		Heap&               heap,
		bool         const  branchDependencies,
		raw_ostream* const  pOut,
		string       const  printPrefix) :
	linFunc          (func),
	_computeBranchDep(branchDependencies),
	_heap            (heap),
	_ownerId         (heap.createOwner()),
	_tracePrinting   (pOut),
	_printPrefix     (printPrefix),
	_out             (_tracePrinting ? *pOut : outs()),
	_instIt          (func.getEntryBlock().begin()),
	_pLastBB         (nullptr),
	_pRecentInst     (nullptr),
	_pNextInst       (&*_instIt),
	_pRetValue       (nullptr) {
	
	unsigned int curIndex = 0;
	
	if(_tracePrinting) {
		_out << _printPrefix << linFunc.func.getName().str();
	}
	
	// Initialize the argument values with the input passed as argument
	for(Argument const& i : func.getArgumentList()) {
		
		int64_t const  value = input[curIndex++];
		Type    const& type  = *i.getType();
		
		if(type.isIntegerTy()) {
			
			APInt apValue(
				type.getIntegerBitWidth(), static_cast<uint64_t>(abs(value)));
			
			// Correct signedness
			if(value < 0) {
				apValue = -apValue;
			}
			
			_state[&i] = new DynInteger(apValue);
			
		} else if(type.isPointerTy()) {
			
			_state[&i] = new DynPointer(static_cast<Heap::AddressType>(value));
			
		} else {
			
			assert(false && "Unsupported argument type");
		}
		
		if(_tracePrinting) {
			_out << (curIndex == 1 ? "(" : ", ");
			_state[&i]->print(_out);
		}
	}
	
	if(_tracePrinting) {
		_out << ")\n";
	}
	
	// Initialize the instruction values with undefined values
	for(Instruction const& i : Util::getInstructions(linFunc.func)) {
		
		switch(i.getType()->getTypeID()) {
			
			case Type::IntegerTyID:
			case Type::PointerTyID:
				_state[&i] = nullptr;
				break;
			
			case Type::VoidTyID:
				break;
			
			default:
				assert(false && "Unsupported instruction value type");
				break;
		}
	}
}

Interpreter::~Interpreter(void) {
	
	// Delete all value objects that have been created during interpretation of
	// the function
	for(TraceEntry const* i : _trace) {
		delete i;
	}
}

void Interpreter::addDependency(
		Value const& dependency) {
	
	// TODO: also consider dependencies on function arguments
	if(Instruction const* pInst = dyn_cast<Instruction>(&dependency)) {
		recentDataDependencies.insert(pInst);
	}
}

DynType const& Interpreter::cloneValue(
		Value const& value) {
	
	switch(value.getType()->getTypeID()) {
		case Type::IntegerTyID:
			return *new DynInteger(resolveInt(value));
		case Type::PointerTyID:
			return *new DynPointer(resolvePointer(value));
		default:
			assert(false && "Type cannot be cloned");
			return UTIL_NULL_REF(DynType const)
	}
}

Heap::AddressType Interpreter::computeArrayElementByteSize(
		Type const& type) {
	
	assert(type.isArrayTy() && "Given type is no array");
	
	return computeByteSize(*dyn_cast<ArrayType>(&type)->getElementType());
}

Heap::AddressType Interpreter::computeByteSize(
		Type const& type) {
	
	ArrayType const* pArrayType;
	
	switch(type.getTypeID()) {
		
		case Type::IntegerTyID:
			return type.getIntegerBitWidth() / 8;
		
		case Type::ArrayTyID:
			pArrayType = dyn_cast<ArrayType>(&type);
			return
				pArrayType->getNumElements() *
				computeByteSize(*pArrayType->getElementType());
		
		case Type::PointerTyID:
			return sizeof(Heap::AddressType);
		
		default:
			assert(false && "Unsupported type");
			return 0;
	}
}

bool Interpreter::execute(
		unsigned long const maxStepCount) {
	
	unsigned long stepCounter = 0;
	
	while(_pNextInst && stepCounter < maxStepCount) {
		executeNextInstruction();
		stepCounter++;
	}
	
	return _pNextInst;
}

bool Interpreter::executeNextInstruction(void) {
	
	// Check whether the end has already been reached
	if(!_pNextInst) return false;
	
	TraceEntry const* pNewTraceEntry;
	
	// Reset the data dependencies, they will be filled during execution of the
	// next instruction by calling 'resolveInt()'
	recentDataDependencies.clear();
	
	if(_pNextInst->isBinaryOp()) {
		
		EXECUTE_INST_1(BinaryOperator)
		
	} else if(_pNextInst->isCast()) {
		
		EXECUTE_INST_1(CastInst)
		
	} else {
		
		switch(_pNextInst->getOpcode()) {
			
			EXECUTE_INST_2(Alloca,        AllocaInst)
			EXECUTE_INST_2(Br,            BranchInst)
			EXECUTE_INST_2(Call,          CallInst)
			EXECUTE_INST_2(GetElementPtr, GetElementPtrInst)
			EXECUTE_INST_2(ICmp,          ICmpInst)
			EXECUTE_INST_2(Load,          LoadInst)
			EXECUTE_INST_2(PHI,           PHINode)
			EXECUTE_INST_2(Ret,           ReturnInst)
			EXECUTE_INST_2(Store,         StoreInst)
			
			default:
				assert(false && "Unsupported instruction type");
				break;
		}
	}
	
	if(_tracePrinting) {
		
		_out << _printPrefix << " > [" <<
			linFunc.indexToString(linFunc[*_pNextInst]) << "] ";
		
		if(pNewTraceEntry->pValue) {
			pNewTraceEntry->pValue->print(_out) << "\n";
		} else if(_pRetValue) {
			_pRetValue->print(_out) << " [return]\n";
		} else {
			_out << "[no value]\n";
		}
		
		for(auto const& i : pNewTraceEntry->heapValues) {
			_out << _printPrefix << "    " << Util::toHexString(i.first, 8) <<
				": " << Util::toHexString(static_cast<uint16_t>(i.second), 2) <<
				"\n";
		}
	}
	
	// Include the branch instructions in the dependencies
	if(_computeBranchDep) {
		
		unordered_set<Instruction const*> branchDependencies;
		
		for(Instruction const* i : recentDataDependencies) {
			if(i->getParent() != _pNextInst->getParent()) {
				branchDependencies.insert(i->getParent()->getTerminator());
			}
		}
		
		recentDataDependencies.insert(
			branchDependencies.begin(), branchDependencies.end());
	}
	
	// Update the execution trace
	_trace.push_back(pNewTraceEntry);
	
	moveToNextInstruction();
	
	return pNewTraceEntry->pValue /*|| pNewTraceEntry*/;
}

Instruction const* Interpreter::getNextInstruction(void) const {
	
	return _pNextInst;
}

Instruction const* Interpreter::getRecentInstruction(void) const {
	
	return _pRecentInst;
}

DynType const* Interpreter::getReturnValue(void) const {
	
	return _pRetValue;
}

void Interpreter::moveToNextInstruction(void) {
	
	_pRecentInst = _pNextInst;
	
	if(isa<ReturnInst>(_pNextInst)) {
		
		_pNextInst = nullptr;
		
	} else {
		
		if(!isa<TerminatorInst>(_pNextInst)) {
			++_instIt;
		}
		
		_pNextInst = &*_instIt;
	}
}

APInt Interpreter::resolveInt(
		Value const& value) {
	
	APInt result;
	
	if(!tryResolveInt(value, result)) {
		assert(false && "Error while resolving integer value");
	}
	
	return result;
}

Heap::AddressType Interpreter::resolvePointer(
		Value const& value) {
	
	Heap::AddressType address;
	
	if(!tryResolvePointer(value, address)) {
		assert(false && "Error while resolving pointer value");
	}
	
	return address;
}

APInt Interpreter::resolveValue(
		Value const& value) {
	
	APInt             intValue;
	Heap::AddressType address;
	
	if(tryResolveInt(value, intValue)) {
		
		return intValue;
		
	} else if(tryResolvePointer(value, address)) {
		
		return APInt(sizeof(Heap::AddressType) * 8, address);
		
	} else {
		
		assert(false && "Error while resolving value");
		return APInt();
	}
}

bool Interpreter::tryResolveInt(
		Value const& value,
		APInt&       result) {
	
	if(_state.find(&value) != _state.end()) {
		
		DynType const& dynValue = *_state[&value];
		
		if(!dynValue.isInteger()) {
			return false;
		}
		
		addDependency(value);
		
		result = dynValue.asInteger().value;
		
	} else if(ConstantInt const* pConstInt = dyn_cast<ConstantInt>(&value)) {
		
		result = pConstInt->getValue();
		
	} else {
		
		return false;
	}
	
	return true;
}

bool Interpreter::tryResolvePointer(
		Value const&       value,
		Heap::AddressType& result) {
	
	if(_state.find(&value) != _state.end()) {
		
		DynType const& dynValue = *_state[&value];
		
		if(!dynValue.isPointer()) {
			return false;
		}
		
		addDependency(value);
		
		result = dynValue.asPointer().heapLocation;
		
	} else if(isa<ConstantPointerNull>(&value)) {
		
		result = 0;
	
	} else {
		
		return false;
	}
	
	return true;
}

TraceEntry const& Interpreter::updateState(
		llvm::Instruction const& inst,
		DynType const*           pValue) {
	
	_state[&inst] = pValue;
	
	return *new TraceEntry(inst, pValue, _heap);
}

TraceEntry const& Interpreter::updateState(
		llvm::Instruction const& inst,
		Heap::AddressType const  address,
		Heap::AddressType const  length) {
	
	return *new TraceEntry(inst, nullptr, _heap, address, length);
}

DynType const& Interpreter::operator[](
		Value const& value) const {
	
	try {
		return *_state.at(&value);
	} catch(out_of_range e) {
		assert(false);
		return *new DynInteger();
	}
}

TraceEntry const& Interpreter::executeAllocaInst(
		AllocaInst const& inst) {
	
	assert(!inst.isArrayAllocation() && "Unsupported alloca operation");
	
	return updateState(
		inst,
		new DynPointer(
			_heap.alloc(_ownerId, computeByteSize(*inst.getAllocatedType()))));
}

TraceEntry const& Interpreter::executeBinaryOperator(
		BinaryOperator const& inst) {
	
	assert(
		inst.getNumOperands() == 2 &&
		"Binary operators need exactly 2 operands");
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveInt(*inst.getOperand(0));
	APInt const op2 = resolveInt(*inst.getOperand(1));
	
	switch(_pNextInst->getOpcode()) {
		
		EXECUTE_BIN_OP(Add,  op1 + op2)
		EXECUTE_BIN_OP(Sub,  op1 - op2)
		EXECUTE_BIN_OP(Mul,  op1 * op2)
		EXECUTE_BIN_OP(And,  op1 & op2)
		EXECUTE_BIN_OP(Or,   op1 | op2)
		EXECUTE_BIN_OP(Xor,  op1 ^ op2)
		EXECUTE_BIN_OP(SDiv, op1.sdiv(op2))
		EXECUTE_BIN_OP(UDiv, op1.udiv(op2))
		EXECUTE_BIN_OP(SRem, op1.srem(op2))
		EXECUTE_BIN_OP(URem, op1.urem(op2))
		EXECUTE_BIN_OP(Shl,  op1.shl (op2))
		EXECUTE_BIN_OP(LShr, op1.lshr(op2))
		EXECUTE_BIN_OP(AShr, op1.ashr(op2))
		
		default:
			assert(false && "Unsupported binary operator");
			return UTIL_NULL_REF(TraceEntry const);
	}
}

TraceEntry const& Interpreter::executeBranchInst(
		BranchInst const& inst) {
	
	unsigned int successorIndex;
	
	if(inst.isUnconditional()) {
		
		assert(inst.getNumSuccessors() == 1);
		successorIndex = 0;
		
	} else {
		
		assert(inst.getNumSuccessors() == 2);
		successorIndex =
			resolveInt(*inst.getCondition()).getBoolValue() ? 0 : 1;
	}
	
	// Move to the next basic block
	_pLastBB = inst.getParent();
	_instIt  = inst.getSuccessor(successorIndex)->begin();
	
	return updateState(inst);
}

TraceEntry const& Interpreter::executeCallInst(
		CallInst const& inst) {
	
	Function const* pCalledFunction = inst.getCalledFunction();
	
	assert(pCalledFunction != nullptr && "Called function not available");
	
	string const functionName = pCalledFunction->getName().str();
	
	if(functionName.find(ExplicitAssignPass::FUNCTION_NAME) == 0 ||
		functionName.find(MarkAnalysisPass::FUNCTION_NAME) == 0) {
		
		assert(
			inst.getNumArgOperands() == 1 &&
			"Special function must take exactly 1 argument");
		
		return updateState(inst, &cloneValue(*inst.getArgOperand(0)));
		
	} else if(functionName.find(Criterion::FUNCTION_NAME) == 0) {
		
		unsigned int const argCount = inst.getNumArgOperands();
		
		for(unsigned int i = 0; i < argCount; i++) {
			addDependency(*inst.getArgOperand(i));
		}
		
		return updateState(inst);
		
	} else {
		
		InputType args(inst.getNumArgOperands());
		
		// Collect arguments
		for(unsigned int i = 0; i < args.size(); i++) {
			
			Value const& arg = *inst.getArgOperand(i);
			
			switch(arg.getType()->getTypeID()) {
				
				case Type::IntegerTyID:
					// TODO: Signedness
					args[i] = static_cast<InputType::value_type>(
						resolveInt(arg).getLimitedValue());
					break;
				
				case Type::PointerTyID:
					args[i] = static_cast<InputType::value_type>(
						resolvePointer(arg));
					break;
				
				default:
					assert(false && "Unsupported argument type");
					break;
			}
		}
		
		Interpreter interpreter(
			*inst.getCalledFunction(),
			args,
			_heap,
			_computeBranchDep,
			_tracePrinting ? &_out : nullptr,
			_printPrefix + "  ");
		
		// Interprete the function
		interpreter.execute();
		
		DynType const* const pFuncRetValue = interpreter.getReturnValue();
		
		return updateState(
			inst, pFuncRetValue ? &pFuncRetValue->clone() : nullptr);
	}
}

TraceEntry const& Interpreter::executeCastInst(
		CastInst const& inst) {
	
	if(inst.isIntegerCast() || inst.getOpcode() == Instruction::IntToPtr) {
		
		APInt value = resolveInt(*inst.getOperand(0));
		
		switch(inst.getOpcode()) {
			
			EXECUTE_CAST_INST_BIT_WIDTH(Trunc, trunc)
			EXECUTE_CAST_INST_BIT_WIDTH(ZExt, zext)
			EXECUTE_CAST_INST_BIT_WIDTH(SExt, sext)
			
			case Instruction::IntToPtr:
				return
					updateState(inst, new DynPointer(value.getLimitedValue()));
			
			default:
				assert(false && "Unsupported integer cast");
				return UTIL_NULL_REF(TraceEntry const);
		}
		
	} else {
		
		Heap::AddressType address = resolvePointer(*inst.getOperand(0));
		
		switch(inst.getOpcode()) {
			
			case Instruction::PtrToInt:
				return updateState(
					inst,
					new DynInteger(
						APInt(inst.getType()->getIntegerBitWidth(), address)));
			
			case Instruction::BitCast:
				return updateState(inst, new DynPointer(address));
			
			default:
				assert(false && "Unsupported pointer cast");
				return UTIL_NULL_REF(TraceEntry const);
		}
	}
}

TraceEntry const& Interpreter::executeGetElementPtrInst(
		GetElementPtrInst const& inst) {
	
	Type const&             srcType = *inst.getSourceElementType();
	User::const_op_iterator curOp   = inst.idx_begin();
	Heap::AddressType       elementSize;
	
	if(srcType.isArrayTy()) {
		
		assert(
			inst.getNumIndices() == 2 &&
			resolveInt(**curOp).getLimitedValue() == 0 &&
			"Unsupported GEP instruction for arrays");
		
		++curOp;
		
		elementSize = computeArrayElementByteSize(srcType);
		
	} else {
		
		assert(
			inst.getNumIndices() == 1 &&
			"Unsupported GEP instruction for non-array types");
		
		elementSize = computeByteSize(srcType);
	}
	
	Heap::AddressType const offset = resolvePointer(*inst.getPointerOperand());
	Heap::AddressType const index  = resolveInt(**curOp).getLimitedValue();
	
	return updateState(inst, new DynPointer(offset + index * elementSize));
}

TraceEntry const& Interpreter::executeICmpInst(
		ICmpInst const& inst) {
	
	assert(
		inst.getNumOperands() == 2 &&
		"Compare instructions need exactly 2 operands");
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveValue(*inst.getOperand(0));
	APInt const op2 = resolveValue(*inst.getOperand(1));
	
	switch(inst.getPredicate()) {
		
		EXECUTE_ICMP_INST(ICMP_EQ,  eq)
		EXECUTE_ICMP_INST(ICMP_NE,  ne)
		EXECUTE_ICMP_INST(ICMP_SGE, sge)
		EXECUTE_ICMP_INST(ICMP_SGT, sgt)
		EXECUTE_ICMP_INST(ICMP_SLE, sle)
		EXECUTE_ICMP_INST(ICMP_SLT, slt)
		EXECUTE_ICMP_INST(ICMP_UGE, uge)
		EXECUTE_ICMP_INST(ICMP_UGT, ugt)
		EXECUTE_ICMP_INST(ICMP_ULE, ule)
		EXECUTE_ICMP_INST(ICMP_ULT, ult)
		
		default:
			assert(false && "Unsupported compare operation");
			return UTIL_NULL_REF(TraceEntry const);
	}
}

TraceEntry const& Interpreter::executeLoadInst(
		LoadInst const& inst) {
	
	Heap::AddressType const  address  =
		resolvePointer(*inst.getPointerOperand());
	Type              const& type     = *inst.getType();
	APInt             const  rawValue = _heap.readInt(
		address,
		static_cast<Heap::SizeType>(computeByteSize(type) * 8),
		&recentDataDependencies);
	
	switch(type.getTypeID()) {
		
		case Type::IntegerTyID:
			return updateState(inst, new DynInteger(rawValue));
		
		case Type::PointerTyID:
			return
				updateState(inst, new DynPointer(rawValue.getLimitedValue()));
		
		default:
			assert(false && "Unsupported load type");
			return UTIL_NULL_REF(TraceEntry const);
	}
}

TraceEntry const& Interpreter::executePHINode(
		PHINode const& inst) {
	
	return updateState(
		inst, &cloneValue(*inst.getIncomingValueForBlock(_pLastBB)));
}

TraceEntry const& Interpreter::executeReturnInst(
		ReturnInst const& inst) {
	
	if(Value const* const pRetValue = inst.getReturnValue()) {
		_pRetValue = &cloneValue(*pRetValue);
	} else {
		_pRetValue = nullptr;
	}
	
	return updateState(inst);
}

TraceEntry const& Interpreter::executeStoreInst(
		StoreInst const& inst) {
	
	Heap::AddressType const  address =
		resolvePointer(*inst.getPointerOperand());
	Value             const& value   = *inst.getValueOperand();
	Type              const& type    = *value.getType();
	
	switch(type.getTypeID()) {
		
		case Type::IntegerTyID:
			_heap.writeInt(address, resolveInt(value), inst);
			return updateState(inst, address, type.getIntegerBitWidth() / 8);
		
		case Type::PointerTyID:
			_heap.writeInt(
				address,
				APInt(sizeof(Heap::AddressType) * 8, resolvePointer(value)),
				inst);
			return updateState(inst, address, sizeof(Heap::AddressType));
		
		default:
			assert(false && "Unsupported store instruction value type");
			return UTIL_NULL_REF(TraceEntry const);
	}
}

TraceEntry::TraceEntry(
		Instruction       const& inst,
		DynType const*    const  pValue,
		Heap              const& heap,
		Heap::AddressType const  address,
		Heap::AddressType const  length) :
	inst  (inst),
	pValue(pValue) {
	
	for(Heap::AddressType i = 0; i < length; i++) {
		heapValues.emplace(address + i, heap[address + i]);
	}
}

TraceEntry::~TraceEntry(void) {
	
	if(pValue) {
		delete pValue;
	}
}

DynInteger const& DynType::asInteger(void) const {
	
	assert(id == Type::IntegerTyID && "Invalid type conversion");
	
	return *static_cast<DynInteger const*>(this);
}

DynInteger& DynType::asInteger(void) {
	
	assert(id == Type::IntegerTyID && "Invalid type conversion");
	
	return *static_cast<DynInteger*>(this);
}

DynPointer const& DynType::asPointer(void) const {
	
	assert(id == Type::PointerTyID && "Invalid type conversion");
	
	return *static_cast<DynPointer const*>(this);
}

DynPointer& DynType::asPointer(void) {
	
	assert(id == Type::PointerTyID && "Invalid type conversion");
	
	return *static_cast<DynPointer*>(this);
}

bool DynType::isInteger(void) const {
	
	return id == Type::IntegerTyID;
}

bool DynType::isPointer(void) const {
	
	return id == Type::PointerTyID;
}

bool DynType::isVoid(void) const {
	
	return id == Type::VoidTyID;
}

DynType::~DynType(void) {}

DynType& DynInteger::clone(void) const {
	
	return *new DynInteger(value);
}

raw_ostream& DynInteger::print(
		raw_ostream& out) const {
	
	return out << value;
}

DynType& DynPointer::clone(void) const {
	
	return *new DynPointer(heapLocation);
}

bool DynPointer::isNull(void) const {
	
	return !heapLocation;
}

raw_ostream& DynPointer::print(
		raw_ostream& out) const {
	
	return out << "p->" << Util::toHexString(heapLocation, 8);
}
