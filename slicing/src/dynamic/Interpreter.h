#pragma once

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

#include <unordered_map>

class Integer {
	
	public:
	
	Integer(llvm::APInt& apInt) : constant(false), pValue(&apInt) {}
	Integer(llvm::ConstantInt const& constInt) :
		constant(true),
		pValue  (new llvm::APInt(constInt.getValue())) {}
	~Integer(void);
	
	private:
	
	bool         const constant;
	llvm::APInt* const pValue;
};

// The input signature equals the function signature
class FunctionInput {
	
	public:
	
	llvm::Function const& func;
};

// This class provides indices for each value in a function, that are used in a
// concrete function state
class FunctionStateTemplate {
	
	public:
	
	llvm::Function const& func;
	
	FunctionStateTemplate(llvm::Function const& func);
	
	unsigned int getValueCount(void) const;
	
	unsigned int operator[](llvm::Value const& value) const;
	
	private:
	
	std::unordered_map<llvm::Value const*, unsigned int> indices;
};

// The state signature is the union of the input signature and all variables
// that occure within the function
class FunctionState {
	
	public:
	
	FunctionStateTemplate const& stateTemplate;
	
	FunctionState(FunctionStateTemplate const& stateTemplate);
	~FunctionState(void);
	
	llvm::APInt& getUIntValue(llvm::Value const& value);
	
	private:
	
	// Array which values are of type APInt or APSInt
	void** values;
};

class Interpreter {
	
	public:
	
	llvm::Function const& func;
	
	Interpreter(FunctionInput const& input);
	
	Interpreter& executeNextInstruction(void);
	
	// Provides the current state
	FunctionState const& getState(void) const;
	
	// Provide the instructions that caused the current state and that will be
	// executed in this state
	llvm::Instruction const* getRecentInstruction(void) const;
	llvm::Instruction const* getNextInstruction  (void) const;
	
	private:
	
	llvm::Instruction const* pRecentInst;
	llvm::Instruction const* pNextInst;
	FunctionState     const* pCurrentState;
	
	Integer& resolveValue(llvm::Value const* pVal);
	
	// There is special function for every instruction type
	void executeBinaryOperator(void);
	void executeBranchInst(void);
	void executePHINode(void);
};
