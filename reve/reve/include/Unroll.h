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

#include "llvm/Analysis/LoopInfo.h"

void peelAtMark(llvm::Function &f, int mark, const BidirBlockMarkMap &marks,
                std::string prefix);

std::set<llvm::BasicBlock *> blocksInLoop(llvm::BasicBlock *start,
                                          const BidirBlockMarkMap &marks);

llvm::BasicBlock *
createUniqueBackedge(llvm::BasicBlock *markedBlock, llvm::BasicBlock *preHeader,
                     const std::vector<llvm::BasicBlock *> &backedgeBlocks,
                     llvm::Function &f);

llvm::BasicBlock *
createPreheader(llvm::BasicBlock *markedBlock,
                const std::vector<llvm::BasicBlock *> &outsideBlocks);
class UnrollPass : public llvm::FunctionPass {
  public:
    static char ID;
    void getAnalysisUsage(llvm::AnalysisUsage &AU) const override;
    bool runOnFunction(llvm::Function &Fun) override;
    UnrollPass() : llvm::FunctionPass(ID) {}
};

void unrollAtMark(llvm::Function &f, int mark, const BidirBlockMarkMap &marks,
                  size_t factor);
