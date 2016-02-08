#include "RemoveMarkPass.h"
#include "Helper.h"
#include "llvm/IR/Constants.h"

llvm::PreservedAnalyses RemoveMarkPass::run(llvm::Function &Fun,
                                            llvm::FunctionAnalysisManager *AM) {
    auto BidirMarkBlockMap = AM->getResult<MarkAnalysis>(Fun);
    std::set<llvm::Instruction *> ToDelete;
    for (auto BBTuple : BidirMarkBlockMap.MarkToBlocksMap) {
        // no need to remove anything in exit and entry nodes
        if (BBTuple.first >= 0) {
            for (auto BB : BBTuple.second) {
                for (auto &Inst : *BB) {
                    if (auto CallInst = llvm::dyn_cast<llvm::CallInst>(&Inst)) {
                        if ((CallInst->getCalledFunction() != nullptr) &&
                            CallInst->getCalledFunction()->getName() ==
                                "__mark") {
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
