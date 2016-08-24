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
#include "llvm/IR/LegacyPassManager.h"

class RemoveMarkRefsPass : public llvm::FunctionPass {
  public:
    static llvm::StringRef name() { return "RemoveMarkRefsPass"; }
    bool runOnFunction(llvm::Function &Fun) override;
    RemoveMarkRefsPass() : llvm::FunctionPass(ID) {}
    static char ID;
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
};

void removeAnd(const llvm::Instruction *Instr, llvm::BinaryOperator *BinOp);
