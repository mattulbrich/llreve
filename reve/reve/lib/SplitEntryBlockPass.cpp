/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SplitEntryBlockPass.h"

bool SplitBlockPass::runOnFunction(llvm::Function &Fun) {
    auto &Entry = Fun.getEntryBlock();
    Entry.splitBasicBlock(Entry.begin());
    std::vector<llvm::Instruction*> splitAt;
    for (auto &BB : Fun) {
        for (auto &Inst : BB) {
            if (const auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                if ((CallInst->getCalledFunction() != nullptr) &&
                    CallInst->getCalledFunction()->getName() == "__splitmark") {
                    splitAt.push_back(CallInst);
                }
            }
        }
    }
    for (auto instr : splitAt) {
        llvm::BasicBlock::iterator i(instr);
        ++i;
        i->getParent()->splitBasicBlock(i);
        instr->getParent()->splitBasicBlock(instr);
    }
    return true;
}

char SplitBlockPass::ID = 0;
static llvm::RegisterPass<SplitBlockPass>
    RegisterMarkAnalysis("split-entry-block", "Split Entry Block", false, false);
