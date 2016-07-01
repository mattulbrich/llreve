#include "Interpreter.h"

#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"

using namespace std;
using namespace llvm;

Integer::~Integer(void) {
	
	if(constant) delete pValue;
}

FunctionStateTemplate::FunctionStateTemplate(
		Function const& func) : func(func) {
	
	
}

unsigned int FunctionStateTemplate::getValueCount(void) const {
	
	return static_cast<unsigned int>(indices.size());
}

unsigned int FunctionStateTemplate::operator[](
		Value const& value) const {
	
	return indices.at(&value);
}

APInt& FunctionState::getUIntValue(
		Value const& value) {
	
	return *static_cast<APInt*>(values[stateTemplate[value]]);
}

FunctionState::FunctionState(
		FunctionStateTemplate const& stateTemplate) :
	stateTemplate(stateTemplate),
	values       (new void*[stateTemplate.getValueCount()]) {
	
	
}

FunctionState::~FunctionState(void) {
	
	// TODO: einzelne Werte löschen
	
	delete [] values;
}

Interpreter& Interpreter::executeNextInstruction(void) {
	
	pRecentInst = pNextInst;
	
	if(isa<BinaryOperator>(pRecentInst)) {
		executeBinaryOperator();
	} else if(isa<BranchInst>(pRecentInst)) {
		executeBranchInst();
	} else if(isa<PHINode>(pRecentInst)) {
		executePHINode();
	} else {
		// TODO: Unsupported instruction
	}
	
	return *this;
}

Instruction const* Interpreter::getNextInstruction(void) const {
	
	return pNextInst;
}

Instruction const* Interpreter::getRecentInstruction(void) const {
	
	return pRecentInst;
}

FunctionState const& Interpreter::getState(void) const {
	
	return *pCurrentState;
}

Integer& Interpreter::resolveValue(
		Value const* pVal) {
	
	if(isa<Instruction>(pVal) || isa<Argument>(pVal)) {
		
		// TODO: resolve
		//return state.variables.at(val);
		
	} else if (auto const constInt = dyn_cast<ConstantInt>(pVal)) {
		
		// For the moment treat all integers, no matter which bit width
		return *new Integer(*constInt);
		
	//} else if (isa<ConstantPointerNull>(val)) {
		//return make_shared<VarInt>(Integer(makeBoundedInt(64, 0)));
	} else {
		
	}
}

void Interpreter::executeBinaryOperator(void) {
	
	Integer& op1 = resolveValue(pRecentInst->getOperand(0));
	Integer& op2 = resolveValue(pRecentInst->getOperand(0));
	
	
	
	delete &op1;
	delete &op2;
}
