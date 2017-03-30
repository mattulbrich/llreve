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

#include "llvm/IR/Instructions.h"

llvm::PreservedAnalyses
SplitBlockPass::run(llvm::Function &Fun, llvm::FunctionAnalysisManager &fam) {
    auto &Entry = Fun.getEntryBlock();
    Entry.splitBasicBlock(Entry.begin());
    std::vector<llvm::Instruction *> splitAt;
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
    return llvm::PreservedAnalyses::none();
}
