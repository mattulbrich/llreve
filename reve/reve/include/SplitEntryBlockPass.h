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

#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"

class SplitBlockPass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "SplitEntryBlockPass"; }
    bool runOnFunction(llvm::Function &Fun);
    SplitBlockPass() : llvm::FunctionPass(ID) {}
    static char ID;
};
