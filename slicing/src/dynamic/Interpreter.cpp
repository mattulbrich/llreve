#include "Interpreter.h"

#include "core/Util.h"
#include "preprocessing/ExplicitAssignPass.h"

#include "llvm/IR/Argument.h"
#include "llvm/IR/User.h"

#include <cassert>
#include <iostream>

#define EXECUTE_INST_1(INST_NAME) \
	pNewValue = execute##INST_NAME(*dyn_cast<INST_NAME const>(_pNextInst));

#define EXECUTE_INST_2(OP_CODE, INST_NAME) \
	case Instruction::OP_CODE: EXECUTE_INST_1(INST_NAME) break;

#define EXECUTE_BIN_OP(OP_CODE, OP) \
	case Instruction::OP_CODE: return new DynInteger(OP);

#define EXECUTE_ICMP_INST(OP_CODE, OP_FUN) \
	case CmpInst::OP_CODE: return new DynInteger(op1.OP_FUN(op2));

using namespace std;
using namespace llvm;

static APInt undefValueAPInt;

DynType&    DynType   ::voidValue  = *new DynType   (Type::VoidTyID, nullptr);
DynInteger& DynInteger::undefValue = *new DynInteger(undefValueAPInt);
DynPointer& DynPointer::nullPtr    = *new DynPointer(DynType::voidValue);

Interpreter::Interpreter(
		Function  const& func,
		InputType const& input,
		bool      const  branchDependencies) :
	func             (func),
	_computeBranchDep(branchDependencies),
	_instIt          (func.getEntryBlock().begin()),
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
		
		_state[&i] = new DynInteger(apValue);
	}
	
	// Initialize the instruction values with undefined values
	for(Instruction const& i : Util::getInstructions(func)) {
		
		if(isIntValue(i)) {
			_state[&i] = &DynInteger::undefValue;
		} else if(isPointerValue(i)) {
			_state[&i] = &DynPointer::nullPtr;
		} else {
			assert(isVoidValue(i) && "Unsupported value type");
		}
		
		_arrays[&i] = nullptr;
	}
}

Interpreter::~Interpreter(void) {
	
	// Delete the integers allocated on the heap;
	for(auto const& i : _trace) {
		if(!i.second->isSpecial()) {
			delete i.second;
		}
	}
	
	// Delete the arrays allocated on the heap
	for(auto const& i : _arrays) {
		delete i.second;
	}
	
	// Delete the return value
	if(_pRetValue) {
		delete _pRetValue;
	}
}

DynType& Interpreter::cloneValue(
		Value const& value) {
	
	if(_state.find(&value) != _state.end()) {
		
		return *_state[&value]->clone();
		
	} else if(auto pConstInt = dyn_cast<ConstantInt>(&value)) {
		
		return *new DynInteger(pConstInt->getValue());
		
	} else if(isa<ConstantPointerNull>(&value)) {
		
		return DynPointer::nullPtr;
		
	} else {
		assert(false);
		return DynType::voidValue;
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
	
	DynType const* pNewValue = nullptr;
	
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
	
	if(pNewValue) {
		pNewValue->print(outs()) << "\n";
	} else {
		outs() << "no value\n";
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
	
	// Update state and execution trace
	_state[_pNextInst] = pNewValue;
	_trace.push_back({_pNextInst, pNewValue});
	
	moveToNextInstruction();
	
	return pNewValue;
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

unsigned int Interpreter::getValueBitWidth(
		Value const& value) {
	
	assert(isIntValue(value));
	
	return value.getType()->getPrimitiveSizeInBits();
}

bool Interpreter::isArrayValue(
		Value const& value) {
	
	return value.getType()->isArrayTy();
}

bool Interpreter::isPointerValue(
		Value const& value) {
	
	return value.getType()->isPointerTy();
}

bool Interpreter::isIntValue(
		Value const& value) {
	
	return value.getType()->isIntegerTy();
}

bool Interpreter::isVoidValue(
		Value const& value) {
	
	return value.getType()->isVoidTy();
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
	
	if(Instruction const* pInst = dyn_cast<Instruction>(pVal)) {
		
		recentDataDependencies.insert(pInst);
		return _state.at(pVal)->asInteger().value;
		
	} else if(isa<Argument>(pVal)) {
		
		return _state.at(pVal)->asInteger().value;
		
	} else if(ConstantInt const* pConstInt = dyn_cast<ConstantInt>(pVal)) {
		
		return pConstInt->getValue();
		
	//} else if (isa<ConstantPointerNull>(val)) {
		//return make_shared<VarInt>(Integer(makeBoundedInt(64, 0)));
	} else {
		
		assert(false && "Error while resolving integer value");
	}
}

DynPointer const& Interpreter::resolvePointer(
		Value const* pVal) {
	
	if(Instruction const* pInst = dyn_cast<Instruction>(pVal)) {
		
		recentDataDependencies.insert(pInst);
		return _state.at(pVal)->asPointer();
		
	} else if(isa<Argument>(pVal)) {
		
		return _state.at(pVal)->asPointer();
		
	} else {
		
		// TODO: const NULL pointer
		
		assert(false && "Error while resolving pointer value");
	}
}

DynType const& Interpreter::operator[](
		Value const& value) const {
	
	try {
		return *_state.at(&value);
	} catch(out_of_range e) {
		return DynType::voidValue;
	}
}

DynType* Interpreter::executeAllocaInst(
		AllocaInst const& inst) {
	
	assert(!_arrays[_pNextInst] && "Array has already been allocated");
	
	assert(
		inst.getAllocatedType()->isArrayTy() && !inst.isArrayAllocation() &&
		"Unsupported alloca operation");
	
	_arrays[_pNextInst] =
		new DynArray(*dyn_cast<ArrayType>(inst.getAllocatedType()));
	
	return new DynPointer(*_arrays[_pNextInst]);
}

DynType* Interpreter::executeBinaryOperator(
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

DynType* Interpreter::executeBranchInst(
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

DynType* Interpreter::executeCallInst(
		CallInst const& inst) {
	
	Function const* pCalledFunction = inst.getCalledFunction();
	
	assert(pCalledFunction != nullptr && "Called function not available");
	
	if(pCalledFunction->getName().str() == ExplicitAssignPass::FUNCTION_NAME) {
		
		assert(
			inst.getNumArgOperands() == 1 &&
			"Special function 'identity' must take exactly 1 argument");
		
		return &cloneValue(*inst.getArgOperand(0));
		
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
		
		return pFuncRetValue ? pFuncRetValue->clone() : nullptr;
	}
}

DynType* Interpreter::executeGetElementPtrInst(
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
		resolvePointer(&*inst.getPointerOperand()).element.asArray();
	
	return new DynPointer(array.getElement(index));
}

DynType* Interpreter::executeICmpInst(
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

DynType* Interpreter::executeLoadInst(
		LoadInst const& inst) {
	
	return new DynInteger(
		resolvePointer(inst.getPointerOperand()).element.asInteger().value);
}

DynType* Interpreter::executePHINode(
		PHINode const& inst) {
	
	return new DynInteger(resolveInt(inst.getIncomingValueForBlock(_pLastBB)));
}

DynType* Interpreter::executeReturnInst(
		ReturnInst const& inst) {
	
	Value const* const pRetValue = inst.getReturnValue();
	
	_pRetValue =
		pRetValue ? new DynInteger(resolveInt(pRetValue)) : nullptr;
	
	return nullptr;
}

DynType* Interpreter::executeStoreInst(
		StoreInst const& inst) {
	
	APInt const value        = resolveInt(inst.getValueOperand());
	DynInteger& arrayElement =
		resolvePointer(inst.getPointerOperand()).element.asInteger();
	DynArray&   array        = arrayElement.pParent->asArray();
	
	array.setElement(arrayElement, *new DynInteger(value, &array));
	
	return nullptr;
}

DynType::~DynType(void) {
	
	if(isSpecial()) {
		assert(false && "Cannot delete special dynamic value");
	}
}

DynType* DynType::clone(
		DynType* const pParent) const {
	
	(void)pParent;
	
	if(!isVoid()) {
		assert(false && "Error while cloning generic value");
	}
	
	return const_cast<DynType*>(this);
}

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

bool DynType::isSpecial(void) const {
	
	return
		this == &voidValue              ||
		this == &DynInteger::undefValue ||
		this == &DynPointer::nullPtr;
}

bool DynType::isVoid(void) const {
	
	return this == &voidValue;
}

raw_ostream& DynType::print(
		raw_ostream& out) const {
	
	return out;
}

DynInteger::~DynInteger(void) {
	
	if(!isUndef()) {
		delete &value;
	}
}

DynType* DynInteger::clone(
		DynType* const pParent) const {
	
	return new DynInteger(value, pParent);
}

bool DynInteger::isUndef(void) const {
	
	return &value == &undefValueAPInt;
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
		ArrayType const& type,
		DynType*  const  pParent) :
	DynType(Type::ArrayTyID, pParent),
	size   (static_cast<unsigned int>(type.getNumElements())) {
	
	Type const& elementType = *type.getElementType();
	
	switch(elementType.getTypeID()) {
		
		case Type::IntegerTyID:
			_array = reinterpret_cast<DynType**>(new DynInteger*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] = &DynInteger::undefValue;
			}
			break;
		
		case Type::ArrayTyID:
			_array = reinterpret_cast<DynType**>(new DynArray*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] =
					new DynArray(*dyn_cast<ArrayType>(&elementType), this);
			}
			break;
		
		case Type::PointerTyID:
			_array = reinterpret_cast<DynType**>(new DynPointer*[size]);
			for(unsigned int i = 0; i < size; i++) {
				_array[i] = &DynPointer::nullPtr;
			}
			break;
		
		default:
			assert(false && "Unsupported array element type");
			break;
	}
	
	for(unsigned int i = 0; i < size; i++) {
		_elementToIndexMap[_array[i]] = i;
	}
}

DynArray::~DynArray(void) {
	
	for(unsigned int i = 0; i < size; i++) {
		if(!_array[i]->isSpecial()) {
			delete _array[i];
		}
	}
	
	delete [] _array;
}

DynType* DynArray::clone(
		DynType* const pParent) const {
	
	(void)pParent;
	assert(false && "Array cloning not supported yet");
	
	return nullptr;
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

void DynArray::setElement(
		DynType const& oldElement,
		DynType&       newElement) {
	
	unsigned int const index = _elementToIndexMap[&oldElement];
	
	assert(&getElement(index) == &oldElement && "Inconsstent dynamic array");
	
	setElement(index, newElement);
	
	_elementToIndexMap.erase(&oldElement);
	_elementToIndexMap[&newElement] = index;
}

DynType* DynPointer::clone(
		DynType* const pParent) const {
	
	return new DynPointer(element, pParent);
}

bool DynPointer::isNull(void) const {
	
	return this == &nullPtr;
}

raw_ostream& DynPointer::print(
		raw_ostream& out) const {
	
	if(isNull()) {
		out << "nil";
	} else {
		out << "p->";
		element.print(out);
	}
	
	return out;
}
