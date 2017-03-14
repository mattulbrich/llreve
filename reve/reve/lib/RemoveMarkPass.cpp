/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "RemoveMarkPass.h"

#include "Helper.h"
#include "PathAnalysis.h"
#include "llvm/IR/Constants.h"

llvm::AnalysisKey RemoveMarkPass::Key;

llvm::PreservedAnalyses RemoveMarkPass::run(llvm::Function &fun,
                                            llvm::FunctionAnalysisManager &am) {
    auto BidirMarkBlockMap = am.getResult<MarkAnalysis>(fun);
    std::set<llvm::Instruction *> ToDelete;
    for (auto BBTuple : BidirMarkBlockMap.MarkToBlocksMap) {
        // no need to remove anything in exit and entry nodes
        if (BBTuple.first >= Mark(0)) {
            for (auto BB : BBTuple.second) {
                for (auto &Inst : *BB) {
                    if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                        if ((CallInst->getCalledFunction() != nullptr) &&
                            (CallInst->getCalledFunction()->getName() ==
                                 "__mark" ||
                             CallInst->getCalledFunction()->getName() ==
                                 "__splitmark")) {
                            ToDelete.insert(CallInst);
                        }
                    }
                }
            }
        }
    }
    for (auto Instr : ToDelete) {
        // kill the call instruction
        Instr->eraseFromParent();
    }
    return llvm::PreservedAnalyses::all();
}
