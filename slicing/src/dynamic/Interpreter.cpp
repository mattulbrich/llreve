#include "Interpreter.h"

#include "core/Util.h"
#include "preprocessing/ExplicitAssignPass.h"

#include "llvm/IR/Argument.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"

#include <cassert>
#include <iostream>

using namespace std;
using namespace llvm;

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
		
		_state[&i] = new APInt(apValue);
	}
	
	// Initialize the instruction values with undefined values
	for(Instruction const& i : Util::getInstructions(func)) {
		if(isIntValue(i)) {
			_state[&i] = &valueUndef;
		}
	}
}

Interpreter::~Interpreter(void) {
	
	// Delete the integers allocated on the heap;
	for(auto const& i : _trace) {
		if(i.second != &valueVoid && i.second != &valueUndef) {
			delete i.second;
		}
	}
	
	// Delete the return value
	if(_pRetValue && _pRetValue != &valueVoid) {
		delete _pRetValue;
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
	
	APInt const* pNewValue = nullptr;
	
	// Reset the data dependencies, they will be filled during execution of the
	// next instruction by calling 'resolveValue()'
	recentDataDependencies.clear();
	
	if(isa<BinaryOperator>(_pNextInst)) {
		pNewValue = new APInt(executeBinaryOperator());
	} else if(isa<BranchInst>(_pNextInst)) {
		executeBranchInst();
	} else if(isa<CallInst>(_pNextInst)) {
		if(isIntValue(*_pNextInst)) {
			pNewValue = new APInt(executeCallInst());
		} else {
			executeCallInst();
		}
	} else if(isa<ICmpInst>(_pNextInst)) {
		pNewValue = new APInt(1, executeICmpInst() ? 1 : 0);
	} else if(isa<PHINode>(_pNextInst)) {
		pNewValue = new APInt(executePHINode());
	} else if(isa<ReturnInst>(_pNextInst)) {
		executeReturnInst();
	} else {
		assert(false);
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

APInt const* Interpreter::getReturnValue(void) const {
	
	return _pRetValue;
}

unsigned int Interpreter::getValueBitWidth(
		Value const& value) const {
	
	assert(isIntValue(value));
	
	return value.getType()->getPrimitiveSizeInBits();
}

bool Interpreter::isIntValue(
		Value const& value) const {
	
	if(value.getType()->isIntegerTy()) {
		return true;
	} else {
		assert(value.getType()->isVoidTy());
		return false;
	}
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

APInt Interpreter::resolveValue(
		Value const* pVal) {
	
	if(Instruction const* pInst = dyn_cast<Instruction>(pVal)) {
		
		recentDataDependencies.insert(pInst);
		return *_state.at(pVal);
		
	} else if(isa<Argument>(pVal)) {
		
		return *_state.at(pVal);
		
	} else if (ConstantInt const* pConstInt = dyn_cast<ConstantInt>(pVal)) {
		
		return pConstInt->getValue();
		
	//} else if (isa<ConstantPointerNull>(val)) {
		//return make_shared<VarInt>(Integer(makeBoundedInt(64, 0)));
	} else {
		
		assert(false);
	}
}

APInt const& Interpreter::operator[](
		Value const& value) const {
	
	try {
		return *_state.at(&value);
	} catch(out_of_range e) {
		return valueVoid;
	}
}

APInt Interpreter::executeBinaryOperator(void) {
	
	assert(_pNextInst->getNumOperands() == 2);
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveValue(_pNextInst->getOperand(0));
	APInt const op2 = resolveValue(_pNextInst->getOperand(1));
	
	switch(_pNextInst->getOpcode()) {
		case Instruction::Add:  return op1 + op2;
		case Instruction::Sub:  return op1 - op2;
		case Instruction::Mul:  return op1 * op2;
		case Instruction::And:  return op1 & op2;
		case Instruction::Or:   return op1 | op2;
		case Instruction::Xor:  return op1 ^ op2;
		case Instruction::SDiv: return op1.sdiv(op2);
		case Instruction::UDiv: return op1.udiv(op2);
		case Instruction::SRem: return op1.srem(op2);
		case Instruction::URem: return op1.urem(op2);
		case Instruction::Shl:  return op1.shl (op2);
		case Instruction::LShr: return op1.lshr(op2);
		case Instruction::AShr: return op1.ashr(op2);
		default:
			assert(false);
			return valueUndef;
	}
}

void Interpreter::executeBranchInst(void) {
	
	BranchInst const& branchInst = *dyn_cast<BranchInst const>(_pNextInst);
	unsigned int      successorIndex;
	
	if(branchInst.isUnconditional()) {
		
		assert(branchInst.getNumSuccessors() == 1);
		successorIndex = 0;
		
	} else {
		
		assert(branchInst.getNumSuccessors() == 2);
		successorIndex =
			resolveValue(branchInst.getCondition()).getBoolValue() ? 0 : 1;
	}
	
	// Move to the next basic block
	_pLastBB = branchInst.getParent();
	_instIt  = branchInst.getSuccessor(successorIndex)->begin();
}

APInt Interpreter::executeCallInst(void) {
	
	CallInst const& callInst        = *dyn_cast<CallInst>(_pNextInst);
	Function const* pCalledFunction = callInst.getCalledFunction();
	
	assert(pCalledFunction != nullptr);
	
	if(pCalledFunction->getName().str() == ExplicitAssignPass::FUNCTION_NAME) {
		
		assert(callInst.getNumArgOperands() == 1);
		
		return resolveValue(callInst.getArgOperand(0));
		
	} else {
		
		InputType args(callInst.getNumArgOperands());
		
		// Collect arguments
		// TODO: Signedness
		for(unsigned int i = 0; i < args.size(); i++) {
			args[i] = resolveValue(callInst.getArgOperand(i)).getLimitedValue();
		}
		
		Interpreter interpreter(*callInst.getCalledFunction(), args);
		
		// Interprete the function
		interpreter.execute();
		
		return *interpreter.getReturnValue();
	}
}

bool Interpreter::executeICmpInst(void) {
	
	assert(_pNextInst->getNumOperands() == 2);
	
	// Get the operands and the variable belonging to this instruction
	APInt const op1 = resolveValue(_pNextInst->getOperand(0));
	APInt const op2 = resolveValue(_pNextInst->getOperand(1));
	
	switch(dyn_cast<CmpInst>(_pNextInst)->getPredicate()) {
		case CmpInst::ICMP_EQ:  return op1.eq (op2);
		case CmpInst::ICMP_NE:  return op1.ne (op2);
		case CmpInst::ICMP_SGE: return op1.sge(op2);
		case CmpInst::ICMP_SGT: return op1.sgt(op2);
		case CmpInst::ICMP_SLE: return op1.sle(op2);
		case CmpInst::ICMP_SLT: return op1.slt(op2);
		case CmpInst::ICMP_UGE: return op1.uge(op2);
		case CmpInst::ICMP_UGT: return op1.ugt(op2);
		case CmpInst::ICMP_ULE: return op1.ule(op2);
		case CmpInst::ICMP_ULT: return op1.ult(op2);
		default:
			assert(false);
			return false;
	}
}

APInt Interpreter::executePHINode(void) {
	
	return resolveValue(
		dyn_cast<PHINode>(_pNextInst)->getIncomingValueForBlock(_pLastBB));
}

void Interpreter::executeReturnInst(void) {
	
	Value const* const pRetValue =
		dyn_cast<ReturnInst>(_pNextInst)->getReturnValue();
	
	_pRetValue = pRetValue ? new APInt(resolveValue(pRetValue)) : &valueVoid;
}
