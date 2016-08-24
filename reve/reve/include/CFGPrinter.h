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

class CFGViewerPass : public llvm::FunctionPass {
  public:
    CFGViewerPass() : llvm::FunctionPass(ID) {}
    bool runOnFunction(llvm::Function &F) override;
    static auto name() -> llvm::StringRef { return "CFGViewerPass"; }
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    static char ID;
};
