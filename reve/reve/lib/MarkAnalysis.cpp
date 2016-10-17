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

#include <iostream>

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

using std::make_pair;
using std::set;

std::string Mark::toString() const { return std::to_string(index); }

char MarkAnalysis::ID = 0;

bool MarkAnalysis::runOnFunction(llvm::Function &Fun) {
    std::map<Mark, set<llvm::BasicBlock *>> MarkedBlocks;
    std::map<llvm::BasicBlock *, set<Mark>> BlockedMarks;
    MarkedBlocks[ENTRY_MARK].insert(&Fun.getEntryBlock());
    BlockedMarks[&Fun.getEntryBlock()].insert(ENTRY_MARK);
    MarkedBlocks[EXIT_MARK].insert(
        getAnalysis<llvm::UnifyFunctionExitNodes>().ReturnBlock);
    BlockedMarks[getAnalysis<llvm::UnifyFunctionExitNodes>().ReturnBlock]
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
    llvm::LoopInfo &LI = getAnalysis<llvm::LoopInfoWrapperPass>().getLoopInfo();
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
    BlockMarkMap = BidirBlockMarkMap(BlockedMarks, MarkedBlocks);
    return false; // Did not modify CFG
}

void MarkAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::UnifyFunctionExitNodes>();
    AU.addRequired<llvm::LoopInfoWrapperPass>();
}

BidirBlockMarkMap MarkAnalysis::getBlockMarkMap() const { return BlockMarkMap; }

static llvm::RegisterPass<MarkAnalysis>
    RegisterMarkAnalysis("mark-analysis", "Mark Analysis", true, true);
