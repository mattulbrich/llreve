//===- ConstantProp.cpp - Code to perform Simple Constant Propagation -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements constant propagation and merging:
//
// Specifically, this:
//   * Converts instructions like "add int 1, 2" into 3
//
// Notice that:
//   * This pass has a habit of making definitions be dead.  It is a good idea
//     to run a DIE pass sometime after running this pass.
//
//===----------------------------------------------------------------------===//
#include "ConstantProp.h"

#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include <set>

llvm::PreservedAnalyses ConstantProp::run(llvm::Function &F,
                                          llvm::FunctionAnalysisManager *AM) {
    std::set<llvm::Instruction *> WorkList;
    for (llvm::inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
        WorkList.insert(&*i);
    }
    bool Changed = false;
    const llvm::DataLayout &DL = F.getParent()->getDataLayout();
    llvm::TargetLibraryInfo TLI =
        AM->getResult<llvm::TargetLibraryAnalysis>(F);

    while (!WorkList.empty()) {
        llvm::Instruction *I = *WorkList.begin();
        WorkList.erase(WorkList.begin()); // Get an element from the worklist...

        if (!I->use_empty()) // Don't muck with dead instructions...
            if (llvm::Constant *C = ConstantFoldInstruction(I, DL, &TLI)) {
                // Add all of the users of this instruction to the worklist,
                // they
                // might
                // be constant propagatable now...
                for (llvm::User *U : I->users())
                    WorkList.insert(llvm::cast<llvm::Instruction>(U));

                // Replace all of the uses of a variable with uses of the
                // constant.
                I->replaceAllUsesWith(C);

                // Remove the dead instruction.
                WorkList.erase(I);
                I->eraseFromParent();
            }
    }
    return llvm::PreservedAnalyses::all();
}
