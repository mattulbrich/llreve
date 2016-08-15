#include "Interpreter.h"

#include "core/Util.h"
#include "preprocessing/ExplicitAssignPass.h"

#include "llvm/IR/Argument.h"
#include "llvm/IR/User.h"

#include <cassert>
#include <iostream>

#define EXECUTE_INST_1(INST_NAME) \
	pChangedSlot = execute##INST_NAME(*dyn_cast<INST_NAME const>(_pNextInst));

#define EXECUTE_INST_2(OP_CODE, INST_NAME) \
	case Instruction::OP_CODE: EXECUTE_INST_1(INST_NAME) break;

#define EXECUTE_BIN_OP(OP_CODE, OP) \
	case Instruction::OP_CODE: return &updateState(inst, OP);

#define EXECUTE_ICMP_INST(OP_CODE, OP_FUN) \
	case CmpInst::OP_CODE: return &updateState(inst, op1.OP_FUN(op2));

using namespace std;
using namespace llvm;

static APInt undefValueAPInt;

Interpreter::Interpreter(
		Function  const& func,
		InputType const& input,
		bool      const  branchDependencies) :
	func             (func),
	_computeBranchDep(branchDependencies),
	_instIt          (func.getEntryBlock().begin()),
	_retValueSlot    (func),
	_pLastBB         (nullptr),
	_pRecentInst     (nullptr),
	_pNextInst       (&*_instIt) {
	
	unsigned int curIndex = 0;
	
	// Initialize the argument values with the input passed as argument
	for(Argument const& i : func.getArgumentList()) {
		
		int64_t const value = input[curIndex++];
		APInt         apValue(
			getValueBitWidth(i), static_cast<uint64_t>(abs(value)));
		
		// Correct signedness
		if(value < 0) {
			apValue = -apValue;
		}
		
		// TODO: Possible memory leak
		_mappedState[&i] = (new DynInteger(i, apValue))->pSlot;
	}
	
	// Initialize the instruction values with undefined values
	for(Instruction const& i : Util::getInstructions(func)) {
		
		switch(i.getType()->getTypeID()) {
			
			case Type::IntegerTyID:
			case Type::PointerTyID:
				_mappedState[&i] = new DataSlot(i);
				break;
			
			case Type::VoidTyID:
				break;
			
			default:
				assert(false && "Unsupported instruction value type");
				break;
		}
		
		_arrays[&i] = nullptr;
	}
	
	// Add all the mapped slots also to the general state
	for(auto& i : _mappedState) {
		_state.insert(i.second);
	}
}

Interpreter::~Interpreter(void) {
	
	// Delete all value objects that have been created during interpretation of
	// the function
	for(TraceEntry const* i : _trace) {
		delete i;
	}
	
	// Delete the arrays allocated on the heap
	for(auto const& i : _arrays) {
		delete i.second;
	}
	
	// Free the pseudo heap
	for(DataSlot const* i : _state) {
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
	
	DataSlot const* pChangedSlot = nullptr;
	
	// Reset the data dependencies, they will be filled during execution of the
	// next instruction by calling 'resolveInt()'
	recentDataDependencies.clear();
	
	if(_pNextInst->isBinaryOp()) {
		
		EXECUTE_INST_1(BinaryOperator)
		
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
	
	if(pChangedSlot) {
		pChangedSlot->print(outs()) << "\n";
	} else {
		outs() << "<no change>\n";
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
	// (The state is implicitely updated by modifying the data slot)
	_trace.push_back(new TraceEntry(*_pNextInst, pChangedSlot));
	
	moveToNextInstruction();
	
	return pChangedSlot;
}

Instruction const* Interpreter::getNextInstruction(void) const {
	
	return _pNextInst;
}

Instruction const* Interpreter::getRecentInstruction(void) const {
	
	return _pRecentInst;
}

DynType const* Interpreter::getReturnValue(void) const {
	
	return _retValueSlot.getContent();
}

unsigned int Interpreter::getValueBitWidth(
		Value const& value) {
	
	assert(value.getType()->isIntegerTy());
	
	return value.getType()->getPrimitiveSizeInBits();
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
		Value const* pVal) {
	
	APInt result;
	
	if(!tryResolveInt(*pVal, result)) {
		assert(false && "Error while resolving integer value");
	}
	
	return result;
}

DataSlot* Interpreter::resolvePointer(
		Value const& value) {
	
	DataSlot* pSlot;
	
	if(!tryResolvePointer(value, pSlot)) {
		assert(false && "Error while resolving pointer value");
	}
	
	return pSlot;
}

DataSlot& Interpreter::resolvePointerNotNull(
		Value const& value) {
	
	DataSlot* const pSlot = resolvePointer(value);
	
	assert(pSlot && "Unexpected null pointer");
	
	return *pSlot;
}

bool Interpreter::tryResolveInt(
		Value const& value,
		APInt&       result) {
	
	if(_mappedState.find(&value) != _mappedState.end()) {
		
		DynType* const pContent = _mappedState[&value]->getContent();
		
		if(!pContent->isInteger()) {
			return false;
		}
		
		addDependency(value);
		
		result = pContent->asInteger().value;
		
	} else if(ConstantInt const* pConstInt = dyn_cast<ConstantInt>(&value)) {
		
		result = pConstInt->getValue();
		
	} else {
		
		return false;
	}
	
	return true;
}

bool Interpreter::tryResolvePointer(
		Value const& value,
		DataSlot*&   result) {
	
	if(_mappedState.find(&value) != _mappedState.end()) {
		
		DynType* const pContent = _mappedState[&value]->getContent();
		
		if(!pContent->isPointer()) {
			return false;
		}
		
		addDependency(value);
		
		result = pContent->asPointer().pPointedSlot;
		
	} else if(isa<ConstantPointerNull>(&value)) {
		
		result = nullptr;
	
	} else {
		
		return false;
	}
	
	return true;
}

DataSlot const& Interpreter::updateState(
		Instruction const& inst,
		APInt       const& value) {
	
	DataSlot& slot = *_mappedState[&inst];
	
	return slot.setContent(*new DynInteger(inst, value, &slot), inst);
}

DataSlot const& Interpreter::updateState(
		Instruction const& inst,
		bool        const  value) {
	
	DataSlot& slot = *_mappedState[&inst];
	
	return slot.setContent(*new DynInteger(inst, value, &slot), inst);
}

DataSlot const& Interpreter::updateState(
		Instruction const& inst,
		DataSlot*   const  pPointedSlot) {
	
	return *(new DynPointer(inst, pPointedSlot, _mappedState[&inst]))->pSlot;
}

DynType const& Interpreter::operator[](
		Value const& value) const {
	
	try {
		return *_mappedState.at(&value)->getContent();
	} catch(out_of_range e) {
		assert(false);
		return *new DynInteger(value);
	}
}

DataSlot const* Interpreter::executeAllocaInst(
		AllocaInst const& inst) {
	
	assert(!inst.isArrayAllocation() && "Unsupported alloca operation");
	
	DynType* pAllocatedObject;
	
	switch(inst.getAllocatedType()->getTypeID()) {
		
		case Type::IntegerTyID:
			pAllocatedObject = new DynInteger(inst);
			_state.insert(pAllocatedObject->pSlot);
			break;
		
		case Type::ArrayTyID:
			assert(!_arrays[_pNextInst] && "Array has already been allocated");
			pAllocatedObject = _arrays[_pNextInst] = new DynArray(
				*dyn_cast<ArrayType>(inst.getAllocatedType()), inst, _state);
			break;
		
		case Type::PointerTyID:
			pAllocatedObject = new DynPointer(inst);
			_state.insert(pAllocatedObject->pSlot);
			break;
		
		default:
			assert(false && "Unsupported alloca type");
			break;
	}
	
	return &updateState(inst, pAllocatedObject->pSlot);
}

DataSlot const* Interpreter::executeBinaryOperator(
		BinaryOperator const& inst) {
	
	assert(
		inst.getNumOperands() == 2 &&
		"Binary operators need exactly 2 operands");
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveInt(inst.getOperand(0));
	APInt const op2 = resolveInt(inst.getOperand(1));
	
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
			return nullptr;
	}
}

DataSlot const* Interpreter::executeBranchInst(
		BranchInst const& inst) {
	
	unsigned int successorIndex;
	
	if(inst.isUnconditional()) {
		
		assert(inst.getNumSuccessors() == 1);
		successorIndex = 0;
		
	} else {
		
		assert(inst.getNumSuccessors() == 2);
		successorIndex = resolveInt(inst.getCondition()).getBoolValue() ? 0 : 1;
	}
	
	// Move to the next basic block
	_pLastBB = inst.getParent();
	_instIt  = inst.getSuccessor(successorIndex)->begin();
	
	return nullptr;
}

DataSlot const* Interpreter::executeCallInst(
		CallInst const& inst) {
	
	Function const* pCalledFunction = inst.getCalledFunction();
	
	assert(pCalledFunction != nullptr && "Called function not available");
	
	if(pCalledFunction->getName().str() == ExplicitAssignPass::FUNCTION_NAME) {
		
		assert(
			inst.getNumArgOperands() == 1 &&
			"Special function 'identity' must take exactly 1 argument");
		
		Value const& value = *inst.getArgOperand(0);
		
		APInt     intValue;
		DataSlot* pSlot;
		
		if(tryResolveInt(value, intValue)) {
			return &updateState(inst, intValue);
		} else if(tryResolvePointer(value, pSlot)) {
			assert(false && "TODO");
			return nullptr;
		} else {
			assert(false && "Error during explicit assign function");
			return nullptr;
		}
		
	} else {
		
		InputType args(inst.getNumArgOperands());
		
		// Collect arguments
		// TODO: Signedness
		for(unsigned int i = 0; i < args.size(); i++) {
			args[i] = resolveInt(inst.getArgOperand(i)).getLimitedValue();
		}
		
		Interpreter interpreter(*inst.getCalledFunction(), args);
		
		// Interprete the function
		interpreter.execute();
		
		DynType const* const pFuncRetValue = interpreter.getReturnValue();
		
		if(pFuncRetValue) {
			
			switch(pFuncRetValue->id) {
				case Type::IntegerTyID:
					return &updateState(inst, pFuncRetValue->asInteger().value);
				case Type::PointerTyID:
					return &updateState(
						inst, pFuncRetValue->asPointer().pPointedSlot);
				default:
					assert(false && "Unsupported return value type");
					return nullptr;
			}
			
		} else {
			
			return nullptr;
		}
	}
}

DataSlot const* Interpreter::executeGetElementPtrInst(
		GetElementPtrInst const& inst) {
	
	assert(
		inst.getNumIndices() == 2 &&
		inst.getSourceElementType()->isArrayTy() &&
		"Unsupported use of GEP instruction");
	
	User::const_op_iterator curOp = inst.idx_begin();
	
	assert(
		resolveInt(*curOp).getLimitedValue() == 0 &&
		"First GEP operand must be 0");
	
	++curOp;
	
	uint64_t const index = resolveInt(*curOp).getLimitedValue();
	DynArray&      array =
		resolvePointerNotNull(*inst.getPointerOperand()).getContent()->asArray();
	
	return &updateState(inst, array.getElement(index).pSlot);
}

DataSlot const* Interpreter::executeICmpInst(
		ICmpInst const& inst) {
	
	assert(
		inst.getNumOperands() == 2 &&
		"Compare instructions need exactly 2 operands");
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveInt(inst.getOperand(0));
	APInt const op2 = resolveInt(inst.getOperand(1));
	
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
			return nullptr;
	}
}

DataSlot const* Interpreter::executeLoadInst(
		LoadInst const& inst) {
	
	DataSlot& slot = resolvePointerNotNull(*inst.getPointerOperand());
	
	// Add precise heap data dependencies
	addDependency(*slot.getLastModifyingValue());
	
	// TODO: Support othe types than integers
	return &updateState(inst, slot.getContent()->asInteger().value);
}

DataSlot const* Interpreter::executePHINode(
		PHINode const& inst) {
	
	return &updateState(
		inst,
		resolveInt(inst.getIncomingValueForBlock(_pLastBB)));
}

DataSlot const* Interpreter::executeReturnInst(
		ReturnInst const& inst) {
	
	if(Value const* const pRetValue = inst.getReturnValue()) {
		
		switch(pRetValue->getType()->getTypeID()) {
			
			case Type::IntegerTyID:
				new DynInteger(inst, resolveInt(pRetValue), &_retValueSlot);
				break;
			
			case Type::PointerTyID:
				new DynPointer(
					inst, resolvePointer(*pRetValue), &_retValueSlot);
				break;
			
			default:
				assert(false && "Unsupported return value type");
				break;
		}
		
		return &_retValueSlot;
		
	} else {
		
		return nullptr;
	}
}

DataSlot const* Interpreter::executeStoreInst(
		StoreInst const& inst) {
	
	DataSlot&    heapSlot = *_mappedState[inst.getPointerOperand()]->
		getContent()->asPointer().pPointedSlot;
	Value const& value    = *inst.getValueOperand();
	
	switch(value.getType()->getTypeID()) {
		
		case Type::IntegerTyID:
			new DynInteger(inst, resolveInt(&value), &heapSlot);
			break;
		
		case Type::PointerTyID:
			new DynPointer(inst, resolvePointer(value), &heapSlot);
			break;
		
		default:
			assert(false && "Unsupported store instruction value type");
			break;
	}
	
	return &heapSlot;
}

TraceEntry::TraceEntry(
		Instruction const&       inst,
		DataSlot    const* const pSlot) :
	inst    (inst),
	pSlot   (pSlot),
	pContent(pSlot ? pSlot->getContent() : nullptr) {
	
	assert((!pSlot || pContent) && "Trace entry has slot without content");
}

TraceEntry::~TraceEntry(void) {
	
	if(pContent) {
		delete pContent;
	}
}
	
DynType::DynType(
		Type::TypeID const  id,
		Value        const& creatingValue,
		bool         const  createNewSlot,
		DataSlot*    const  pExistingSlot) :
	id         (id),
	parentValue(creatingValue),
	pSlot      (createNewSlot ? new DataSlot(creatingValue) : pExistingSlot) {
	
	assert(!(createNewSlot && pExistingSlot));
	
	if(pSlot) {
		pSlot->setContent(*this, creatingValue);
	}
}

DynType::~DynType(void) {}

DynArray const& DynType::asArray(void) const {
	
	assert(id == Type::ArrayTyID && "Invalid type conversion");
	
	return *static_cast<DynArray const*>(this);
}

DynArray& DynType::asArray(void) {
	
	assert(id == Type::ArrayTyID && "Invalid type conversion");
	
	return *static_cast<DynArray*>(this);
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

bool DynType::isArray(void) const {
	
	return id == Type::ArrayTyID;
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

raw_ostream& DynType::print(
		raw_ostream& out) const {
	
	return out;
}

DynInteger::~DynInteger(void) {
	
	delete &value;
}

bool DynInteger::isUndef(void) const {
	
	return undef;
}

raw_ostream& DynInteger::print(
		raw_ostream& out) const {
	
	if(isUndef()) {
		out << "u";
	} else {
		out << value;
	}
	
	return out;
}

DynArray::DynArray(
		ArrayType          const& type,
		Value              const& creatingValue,
		unordered_set<DataSlot*>& slotSet) :
	DynType(Type::ArrayTyID, creatingValue, true, nullptr),
	size   (static_cast<unsigned int>(type.getNumElements())) {
	
	Type const& elementType = *type.getElementType();
	
	slotSet.insert(pSlot);
	
	switch(elementType.getTypeID()) {
		
		case Type::IntegerTyID:
			_array = reinterpret_cast<DynType**>(new DynInteger*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] = new DynInteger(creatingValue);
			}
			break;
		
		case Type::ArrayTyID:
			_array = reinterpret_cast<DynType**>(new DynArray*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] = new DynArray(
					*dyn_cast<ArrayType>(&elementType), creatingValue, slotSet);
			}
			break;
		
		case Type::PointerTyID:
			_array = reinterpret_cast<DynType**>(new DynPointer*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] = new DynPointer(creatingValue);
			}
			break;
		
		default:
			assert(false && "Unsupported array element type");
			break;
	}
	
	if(elementType.getTypeID() != Type::ArrayTyID) {
		for(unsigned int i = 0; i < size; i++) {
			slotSet.insert(_array[i]->pSlot);
		}
	}
}

DynArray::~DynArray(void) {
	
	Util::deleteArrayDeep(_array, size);
}

DynType& DynArray::getElement(
		unsigned int const index) const {
	
	assert(index >= 0 && index < size && "Index out of range");
	
	return *_array[index];
}

raw_ostream& DynArray::print(
		raw_ostream& out) const {
	
	if(size > 0) {
		
		out << "[";
		
		for(unsigned int i = 0; i < size - 1; i++) {
			_array[0]->print(out) << ",";
		}
		
		_array[size - 1]->print(out) << "]";
		
	} else {
		
		out << "[]";
	}
	
	return out;
}

void DynArray::setElement(
		unsigned int const index,
		DynType&           element) {
	
	assert(index >= 0 && index < size && "Index out of range");
	
	_array[index] = &element;
}

DynType& DynPointer::getSlotContent(void) const {
	
	DynType* const pContent = tryGetSlotContent();
	
	assert(pContent && "Pointed slot is empty");
	
	return *pContent;
}

bool DynPointer::isNull(void) const {
	
	return !pPointedSlot;
}

DynType* DynPointer::tryGetSlotContent(void) const {
	
	assert(!isNull() && "Null pointer cannot be dereferenced");
	
	return pPointedSlot->getContent();
}

raw_ostream& DynPointer::print(
		raw_ostream& out) const {
	
	if(isNull()) {
		out << "nil";
	} else {
		out << "p->";
		pPointedSlot->print(out);
	}
	
	return out;
}

DynType* DataSlot::getContent(void) const {
	
	return pContent;
}

Value const* DataSlot::getLastModifyingValue(void) const {
	
	return pLastModifyingValue;
}

raw_ostream& DataSlot::print(
		raw_ostream& out) const {
	
	out << "(";
	
	if(pContent) {
		pContent->print(out);
	}
	
	out << ")";
	
	return out;
}

DataSlot& DataSlot::setContent(
		DynType&     content,
		Value const& modifyingValue) {
	
	pContent            = &content;
	pLastModifyingValue = &modifyingValue;
	
	return *this;
}
