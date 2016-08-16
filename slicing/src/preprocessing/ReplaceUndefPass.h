#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IntrinsicInst.h"
#include <set>

class ReplaceUndefPass : public llvm::FunctionPass {
public:
	static char ID;

	ReplaceUndefPass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &function) override;

private:
};
