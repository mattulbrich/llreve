#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

#include "UniqueNamePass.h"

using llvm::PreservedAnalyses;

PreservedAnalyses UniqueNamePass::run(llvm::Function &F,
                                          llvm::FunctionAnalysisManager *AM) {
    return PreservedAnalyses::none();
}
