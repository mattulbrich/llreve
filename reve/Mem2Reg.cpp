#include "llvm/Transforms/Scalar.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "Mem2Reg.h"

using namespace llvm;

llvm::PreservedAnalyses PromotePass::run(Function &F,
                                         FunctionAnalysisManager *AM) {
    std::vector<AllocaInst *> Allocas;

    BasicBlock &BB = F.getEntryBlock(); // Get the entry node for the function

    DominatorTree &DT = AM->getResult<DominatorTreeAnalysis>(F);
    AssumptionCache &AC = AM->getResult<AssumptionAnalysis>(F);

    while (1) {
        Allocas.clear();

        // Find allocas that are safe to promote, by looking at all instructions
        // in
        // the entry node
        for (BasicBlock::iterator I = BB.begin(), E = --BB.end(); I != E; ++I)
            if (AllocaInst *AI = dyn_cast<AllocaInst>(I)) // Is it an alloca?
                if (isAllocaPromotable(AI))
                    Allocas.push_back(AI);

        if (Allocas.empty())
            break;

        PromoteMemToReg(Allocas, DT, nullptr, &AC);
    }

    return llvm::PreservedAnalyses::none();
}
