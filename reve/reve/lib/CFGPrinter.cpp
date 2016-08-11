/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "CFGPrinter.h"

#include "llvm/IR/Function.h"

bool CFGViewerPass::runOnFunction(llvm::Function &F) {
    F.viewCFG();
    return false;
}

void CFGViewerPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
}

char CFGViewerPass::ID = 0;
static llvm::RegisterPass<CFGViewerPass>
    RegisterMarkAnalysis("cfgviewerpass", "View CFG", true, true);
