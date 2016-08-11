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

#include "MarkAnalysis.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class RemoveMarkPass : public llvm::FunctionPass {
  public:
    static char ID;
    static llvm::StringRef name() { return "RemoveMarkPass"; }
    bool runOnFunction(llvm::Function &Fun) override;
    RemoveMarkPass() : llvm::FunctionPass(ID) {}
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
};
