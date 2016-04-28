#include "MarkAnalysis.h"

#include <iostream>

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

using std::make_pair;
using std::set;

char MarkAnalysis::ID = 0;

bool MarkAnalysis::runOnFunction(llvm::Function &Fun) {
    std::map<int, set<llvm::BasicBlock *>> MarkedBlocks;
    std::map<llvm::BasicBlock *, set<int>> BlockedMarks;
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
                    CallInst->getCalledFunction()->getName() == "__mark") {
                    const llvm::Value *IDVal = CallInst->getArgOperand(0);
                    int ID = 0;
                    if (const auto ConstInt =
                            llvm::dyn_cast<llvm::ConstantInt>(IDVal)) {
                        ID = static_cast<int>(
                            ConstInt->getValue().getSExtValue());
                    }
                    // the [] operator constructs an element using the default
                    // constructor if it doesn't exist, so we don't need to
                    // check for that here
                    MarkedBlocks[ID].insert(&BB);
                    BlockedMarks[&BB].insert(ID);
                }
            }
        }
        if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator())) {
            MarkedBlocks[UNREACHABLE_MARK].insert(&BB);
            BlockedMarks[&BB].insert(UNREACHABLE_MARK);
        }
    }
    BlockMarkMap = BidirBlockMarkMap(BlockedMarks, MarkedBlocks);
    return false; // Did not modify CFG
}

void MarkAnalysis::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::UnifyFunctionExitNodes>();
}

BidirBlockMarkMap MarkAnalysis::getBlockMarkMap() const { return BlockMarkMap; }

static llvm::RegisterPass<MarkAnalysis>
    RegisterMarkAnalysis("mark-analysis", "Mark Analysis", true, true);
