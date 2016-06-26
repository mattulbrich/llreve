#pragma once

#include "llvm/Pass.h"

/**
 * This class is to set a fixed value for the names of basic blocks
 * and instruction. Fixed values, increase readability of diffs of
 * the program and its slice
 */
class FixNamesPass : public llvm::ModulePass {
public:
	static char ID;

	FixNamesPass() : llvm::ModulePass(ID) {}
	virtual bool runOnModule(llvm::Module &module) override;
};
