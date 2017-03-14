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

class RemoveMarkRefsPass : public llvm::PassInfoMixin<RemoveMarkRefsPass> {
  public:
    llvm::PreservedAnalyses run(llvm::Function &Fun,
                                llvm::FunctionAnalysisManager &am);

  private:
    friend llvm::AnalysisInfoMixin<RemoveMarkRefsPass>;
    static llvm::AnalysisKey Key;
};

void removeAnd(const llvm::Instruction *Instr, llvm::BinaryOperator *BinOp);
