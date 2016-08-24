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

#include "llvm/IR/LegacyPassManager.h"

class InlinePass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "MarkAnalysis"; }
    bool runOnFunction(llvm::Function &fun);
    static char ID;
    InlinePass() : llvm::FunctionPass(ID) {}
};
