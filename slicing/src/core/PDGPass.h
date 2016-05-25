#pragma once

#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include <unordered_map>
#include <unordered_set>

// Computes the PDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class PDGPass : public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	PDGPass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	
	virtual bool runOnFunction(llvm::Function &func) override;
	
	// Return: The instruction 'instr' is control dependent on or NULL if such
	//         an instruction doesn't exist
	llvm::Instruction* getCtrlDependency(
		llvm::Instruction const& instr) const;
	
	// Return: The set passed as 'result'
	// Note:   The result-set needs to be cleared outside the method
	std::unordered_set<llvm::Instruction*>& getDataDependencies(
		llvm::Instruction const&                instr,
		std::unordered_set<llvm::Instruction*>& result =
			*new std::unordered_set<llvm::Instruction*>()) const;
	
	// Return: The set passed as 'result'
	// Note:   The result-set needs to be cleared outside the method
	std::unordered_set<llvm::Instruction*>& getDependencies(
		llvm::Instruction const&                instr,
		std::unordered_set<llvm::Instruction*>& result =
			*new std::unordered_set<llvm::Instruction*>()) const;
	
	private:
	
	std::unordered_map<llvm::BasicBlock const*, llvm::Instruction*>
		_ctrlDependencies;
	
	static llvm::BasicBlock* computeCtrlDependency(
		llvm::BasicBlock const&        bb,
		llvm::PostDominatorTree const& pdt);
};
