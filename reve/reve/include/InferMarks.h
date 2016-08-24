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

#include "llvm/IR/LegacyPassManager.h"

#include <map>
#include <set>

class InferMarksAnalysis : public llvm::FunctionPass {
  public:
    using Result = BidirBlockMarkMap;
    static llvm::StringRef name() { return "InferMarksAnalysis"; }
    bool runOnFunction(llvm::Function &Fun) override;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    BidirBlockMarkMap getBlockMarkMap() const;
    InferMarksAnalysis() : llvm::FunctionPass(ID) {}
    static char ID;
    // it’s not possible to have non default constructors with the legacy
    // passmanager so we can’t just pass a pointer there to escape this
    BidirBlockMarkMap BlockMarkMap;
};
