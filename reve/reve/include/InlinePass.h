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

#include "llvm/IR/PassManager.h"

class InlinePass : public llvm::PassInfoMixin<InlinePass> {
  public:
    llvm::PreservedAnalyses run(llvm::Function &fun,
                                llvm::FunctionAnalysisManager &fam);
};
