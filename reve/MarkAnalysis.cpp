#include "MarkAnalysis.h"
#include "UnifyFunctionExitNodes.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

using std::make_pair;
using std::set;

char MarkAnalysis::PassID;

BidirBlockMarkMap
MarkAnalysis::run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM) {
    std::map<int, set<llvm::BasicBlock *>> MarkedBlocks;
    std::map<llvm::BasicBlock *, set<int>> BlockedMarks;
    MarkedBlocks[ENTRY_MARK].insert(&Fun.getEntryBlock());
    BlockedMarks[&Fun.getEntryBlock()].insert(ENTRY_MARK);
    MarkedBlocks[EXIT_MARK].insert(AM->getResult<UnifyFunctionExitNodes>(Fun));
    BlockedMarks[AM->getResult<UnifyFunctionExitNodes>(Fun)].insert(EXIT_MARK);
    for (auto &BB : Fun) {
        for (auto &Inst : BB) {
            if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                if ((CallInst->getCalledFunction() != nullptr) &&
                    CallInst->getCalledFunction()->getName() == "__mark") {
                    llvm::Value *IDVal = CallInst->getArgOperand(0);
                    int ID = 0;
                    if (auto ConstInt =
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
    return BidirBlockMarkMap(BlockedMarks, MarkedBlocks);
}
