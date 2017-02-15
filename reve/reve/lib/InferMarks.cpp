/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "InferMarks.h"

#include <iostream>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

using std::make_pair;
using std::set;

char InferMarksAnalysis::ID = 0;

bool InferMarksAnalysis::runOnFunction(llvm::Function &Fun) {
    std::map<Mark, set<llvm::BasicBlock *>> MarkedBlocks;
    std::map<llvm::BasicBlock *, set<Mark>> BlockedMarks;
    MarkedBlocks[ENTRY_MARK].insert(&Fun.getEntryBlock());
    BlockedMarks[&Fun.getEntryBlock()].insert(ENTRY_MARK);
    MarkedBlocks[EXIT_MARK].insert(
        getAnalysis<llvm::UnifyFunctionExitNodes>().ReturnBlock);
    BlockedMarks[getAnalysis<llvm::UnifyFunctionExitNodes>().ReturnBlock]
        .insert(EXIT_MARK);
    llvm::LoopInfo &loopInfo =
        getAnalysis<llvm::LoopInfoWrapperPass>().getLoopInfo();
    int i = 1;
    for (auto loop : loopInfo) {
        MarkedBlocks.insert({Mark(i), {loop->getHeader()}});
        BlockedMarks.insert({loop->getHeader(), {Mark(i)}});
        ++i;
    }

    BlockMarkMap = BidirBlockMarkMap(BlockedMarks, MarkedBlocks);
    return false; // Did not modify CFG
}

void InferMarksAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::UnifyFunctionExitNodes>();
    AU.addRequired<llvm::LoopInfoWrapperPass>();
}

BidirBlockMarkMap InferMarksAnalysis::getBlockMarkMap() const {
    return BlockMarkMap;
}

static llvm::RegisterPass<InferMarksAnalysis>
    RegisterInferMarksAnalysis("infer-mark-analysis", "Mark Analysis", true,
                               true);
