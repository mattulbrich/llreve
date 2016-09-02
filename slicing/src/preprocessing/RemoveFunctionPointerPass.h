#pragma once

#include "llvm/IR/LegacyPassManager.h"

class RemoveFunctionPointerPass : public llvm::FunctionPass {
public:
	static char ID;

	RemoveFunctionPointerPass() : llvm::FunctionPass(ID) {}
	virtual bool runOnFunction(llvm::Function &function) override;

private:
};
