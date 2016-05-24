#pragma once

#include "PDGPass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

class SyntacticSlicePass : public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	SyntacticSlicePass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	
	virtual bool runOnFunction(llvm::Function &func) override;
};
