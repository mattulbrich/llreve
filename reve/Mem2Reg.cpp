#include "Mem2Reg.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

llvm::PreservedAnalyses PromotePass::run(llvm::Function &F,
                                         llvm::FunctionAnalysisManager *AM) {
    std::vector<llvm::AllocaInst *> Allocas;

    llvm::BasicBlock &BB =
        F.getEntryBlock(); // Get the entry node for the function

    llvm::DominatorTree &DT = AM->getResult<llvm::DominatorTreeAnalysis>(F);
    llvm::AssumptionCache &AC = AM->getResult<llvm::AssumptionAnalysis>(F);

    while (true) {
        Allocas.clear();

        // Find allocas that are safe to promote, by looking at all instructions
        // in
        // the entry node
        for (llvm::BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E;
             ++I) {
            if (const auto AI =
                    llvm::dyn_cast<llvm::AllocaInst>(I)) { // Is it an alloca?
                if (llvm::isAllocaPromotable(AI)) {
                    Allocas.push_back(AI);
                }
            }
        }

        if (Allocas.empty()) {
            break;
        }

        llvm::PromoteMemToReg(Allocas, DT, nullptr, &AC);
    }

    return llvm::PreservedAnalyses::none();
}
