#include "MarkAnalysis.h"
#include "UnifyFunctionExitNodes.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

using std::make_pair;

char MarkAnalysis::PassID;

std::map<int, llvm::BasicBlock *>
MarkAnalysis::run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM) {
    std::map<int, llvm::BasicBlock *> MarkedBlocks;
    // insert entry block
    MarkedBlocks.insert(make_pair(-1, &Fun.getEntryBlock()));
    MarkedBlocks.insert(make_pair(-2, AM->getResult<UnifyFunctionExitNodes>(Fun)));
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
                    MarkedBlocks.insert(make_pair(ID, &BB));
                    continue;
                }
            }
        }
    }
    return MarkedBlocks;
}
