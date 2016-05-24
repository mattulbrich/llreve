#pragma once

#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include <unordered_map>
#include <unordered_set>

class PDGPass : public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	PDGPass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	
	virtual bool runOnFunction(llvm::Function &func) override;
	
	// Returns the entry point if the instruction is the entry point itself
	llvm::Instruction* getCtrlDependency(
		llvm::Instruction const& instr) const;
	
	// The set passed as argument will be returned for method chaining
	std::unordered_set<llvm::Instruction*>& getDataDependencies(
		llvm::Instruction const&                instr,
		std::unordered_set<llvm::Instruction*>& result =
			*new std::unordered_set<llvm::Instruction*>()) const;
	
	// The set passed as argument will be returned for method chaining
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
