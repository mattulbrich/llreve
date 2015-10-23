#include "MarkAnalysis.h"
#include "UnifyFunctionExitNodes.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"

char MarkAnalysis::PassID;

std::map<llvm::BasicBlock *, int>
MarkAnalysis::run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM) {
    std::map<llvm::BasicBlock *, int> MarkedBlocks;
    // insert entry block
    MarkedBlocks.insert(std::pair<llvm::BasicBlock *, int>(&Fun.getEntryBlock(), -1));
    MarkedBlocks.insert(std::pair<llvm::BasicBlock *, int>(AM->getResult<UnifyFunctionExitNodes>(Fun), -2));
    for (auto &BB : Fun) {
        for (auto &Inst : BB) {
            if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                if (CallInst->getCalledFunction() &&
                    CallInst->getCalledFunction()->getName() == "__mark") {
                    llvm::Value *IDVal = CallInst->getArgOperand(0);
                    int ID = 0;
                    if (auto ConstInt =
                            llvm::dyn_cast<llvm::ConstantInt>(IDVal)) {
                        ID = static_cast<int>(
                            ConstInt->getValue().getSExtValue());
                    }
                    MarkedBlocks.insert(
                        std::pair<llvm::BasicBlock *, int>(&BB, ID));
                    continue;
                }
            }
        }
    }
    return MarkedBlocks;
}
