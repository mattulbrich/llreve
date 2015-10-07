#ifndef UNIQUE_NAME_PASS_H
#define UNIQUE_NAME_PASS_H

#include "llvm/IR/PassManager.h"

struct UniqueNamePass {
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "UniqueNamePass"; }
};

#endif // UNIQUE_NAME_PASS_H
