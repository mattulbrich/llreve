#pragma once

#include "llvm/ADT/APInt.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"

#include <initializer_list>
#include <list>
#include <unordered_map>
#include <unordered_set>
#include <vector>

class Interpreter {
	
	public:
	
	llvm::Function const& func;
	llvm::APInt    const  valueVoid;
	llvm::APInt    const  valueUndef;
	
	std::unordered_set<llvm::Instruction const*> recentDataDependencies;
	
	Interpreter(
		llvm::Function const& func,
		uint64_t       const  input[]);
	~Interpreter(void);
	
	// Return value indicates whether the interpretation has termated before
	// 'maxStepCount' has been reached
	bool execute(
		unsigned long const maxStepCount = static_cast<unsigned long>(-1));
	
	// Return value indicates whether the execution has changed the state
	bool executeNextInstruction(void);
	
	// Provide the instructions that caused the current state and that will be
	// executed in this state
	llvm::Instruction const* getRecentInstruction(void) const;
	llvm::Instruction const* getNextInstruction  (void) const;
	
	llvm::APInt const* getReturnValue(void) const;
	
	llvm::APInt const& operator[](llvm::Value const& value) const;
	
	private:
	
	llvm::BasicBlock::const_iterator _instIt;
	
	llvm::Instruction const* _pRecentInst;
	llvm::Instruction const* _pNextInst;
	llvm::APInt       const* _pRetValue;
	
	std::unordered_map<llvm::Value const*, llvm::APInt const*>         _state;
	std::list<std::pair<llvm::Instruction const*, llvm::APInt const*>> _trace;
	
	unsigned int getValueBitWidth(llvm::Value const& value) const;
	bool         isIntValue      (llvm::Value const& value) const;
	llvm::APInt  resolveValue    (llvm::Value const* pVal);
	
	void moveToNextInstruction(void);
	
	// There is special function for every instruction type
	llvm::APInt executeBinaryOperator(void);
	void        executeBranchInst(void);
	llvm::APInt executeCallInst(void);
	bool        executeICmpInst(void);
	llvm::APInt executePHINode(void);
	void        executeReturnInst(void);
};
