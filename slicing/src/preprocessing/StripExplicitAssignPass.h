/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

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
