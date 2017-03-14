/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "MarkAnalysis.h"

#include "Helper.h"
#include "UnifyFunctionExitNodes.h"

#include <iostream>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

using std::make_pair;
using std::set;

std::string Mark::toString() const { return std::to_string(index); }

bool Mark::hasInvariant() const {
    return noneOf(*this, EXIT_MARK, UNREACHABLE_MARK, FORBIDDEN_MARK);
}

llvm::AnalysisKey MarkAnalysis::Key;

BidirBlockMarkMap MarkAnalysis::run(llvm::Function &Fun,
                                    llvm::FunctionAnalysisManager &am) {
    // This analysis should only ever run once
    if (!firstRun) {
        return blockMarkMap;
    }
    firstRun = false;
    std::map<Mark, set<llvm::BasicBlock *>> MarkedBlocks;
    std::map<llvm::BasicBlock *, set<Mark>> BlockedMarks;
    MarkedBlocks[ENTRY_MARK].insert(&Fun.getEntryBlock());
    BlockedMarks[&Fun.getEntryBlock()].insert(ENTRY_MARK);
    MarkedBlocks[EXIT_MARK].insert(
        am.getResult<FunctionExitNodeAnalysis>(Fun).returnBlock);
    BlockedMarks[am.getResult<FunctionExitNodeAnalysis>(Fun).returnBlock]
        .insert(EXIT_MARK);
    for (auto &BB : Fun) {
        for (auto &Inst : BB) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                if ((CallInst->getCalledFunction() != nullptr) &&
                    (CallInst->getCalledFunction()->getName() == "__mark" ||
                     CallInst->getCalledFunction()->getName() ==
                         "__splitmark")) {
                    const llvm::Value *IDVal = CallInst->getArgOperand(0);
                    int ID = 0;
                    if (const auto ConstInt =
                            llvm::dyn_cast<llvm::ConstantInt>(IDVal)) {
                        ID = static_cast<int>(
                            ConstInt->getValue().getSExtValue());
                    }
                    // TODO does defaulting to 0 make sense here?
                    MarkedBlocks[Mark(ID)].insert(&BB);
                    BlockedMarks[&BB].insert(Mark(ID));
                }
            }
        }
        if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator())) {
            MarkedBlocks[UNREACHABLE_MARK].insert(&BB);
            BlockedMarks[&BB].insert(UNREACHABLE_MARK);
        }
    }
    // loop rotation duplicates marks, so we need to remove the marks that are
    // outside the loop
    llvm::LoopInfo &LI = am.getResult<llvm::LoopAnalysis>(Fun);
    for (auto it : MarkedBlocks) {
        set<llvm::BasicBlock *> newMarkedBlocks;
        if (it.second.size() > 1) {
            for (auto block : it.second) {
                if (LI.getLoopFor(block)) {
                    newMarkedBlocks.insert(block);
                } else {
                    BlockedMarks.at(block).erase(it.first);
                    if (BlockedMarks.at(block).empty()) {
                        BlockedMarks.erase(block);
                    }
                }
            }
            assert(newMarkedBlocks.size() == 1);
            it.second = newMarkedBlocks;
        }
    }
    blockMarkMap = BidirBlockMarkMap(BlockedMarks, MarkedBlocks);
    return blockMarkMap;
}
