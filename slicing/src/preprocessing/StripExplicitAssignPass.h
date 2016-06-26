#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Function.h"

#include <unordered_map>

class StripExplicitAssignPass : public llvm::ModulePass {
public:
	static char ID;

	StripExplicitAssignPass() : llvm::ModulePass(ID) {}
	virtual bool runOnModule(llvm::Module &module) override;

};
