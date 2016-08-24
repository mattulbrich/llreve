/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "InstCombine.h"

#include "PathAnalysis.h"

#include "llvm/IR/Constants.h"

bool InstCombinePass::runOnFunction(llvm::Function &Fun) {
    for (auto &BB : Fun) {
        for (auto &Instr : BB) {
            // Casting a i1 to an i32 and then comparing to 0 is a noop
            if (auto ICmpInst = llvm::dyn_cast<llvm::ICmpInst>(&Instr)) {
                if (ICmpInst->getPredicate() ==
                    llvm::CmpInst::Predicate::ICMP_NE) {
                    // Swap constant to the right
                    if (auto Const = llvm::dyn_cast<llvm::ConstantInt>(
                            ICmpInst->getOperand(0))) {
                        if (Const->isZero()) {
                            ICmpInst->swapOperands();
                        }
                    }
                    if (auto ZExt = llvm::dyn_cast<llvm::ZExtInst>(
                            ICmpInst->getOperand(0))) {
                        if (ZExt->getOperand(0)->getType()->isIntegerTy(1)) {
                            auto Op = ZExt->getOperand(0);
                            for (auto User : ICmpInst->users()) {
                                User->replaceUsesOfWith(ICmpInst, Op);
                            }
                        }
                    }
                }
            }
        }
    }
    return true;
}

char InstCombinePass::ID = 0;

static llvm::RegisterPass<InstCombinePass>
    RegisterMarkAnalysis("inst-combine-pass", "Combine instructions", false,
                         false);

void InstCombinePass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.addPreserved<MarkAnalysis>();
    AU.addPreserved<PathAnalysis>();
    AU.setPreservesCFG();
}
