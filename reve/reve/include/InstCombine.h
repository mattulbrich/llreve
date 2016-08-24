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
#include "llvm/IR/PassManager.h"

class InstCombinePass : public llvm::FunctionPass {
 public:
    static llvm::StringRef name() {
        return "InstCombinePass";
    }
    bool runOnFunction(llvm::Function &Fun) override;
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    InstCombinePass() : llvm::FunctionPass(ID) {}
    static char ID;
};
