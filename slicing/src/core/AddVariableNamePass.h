#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"

class AddVariableNamePass : public llvm::FunctionPass {
public:
	static char ID;

	AddVariableNamePass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &Fun) override;
	virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;

	static llvm::DIVariable* getSrcVariable(llvm::Instruction& instruction);

private:
	llvm::DIVariable* findSrcVariable(const llvm::Instruction& instruction);
	void setSrcVariable(llvm::Instruction& instruction, llvm::DIVariable* variable);

};
