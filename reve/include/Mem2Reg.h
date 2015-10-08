#ifndef MEM_2_REG_H
#define MEM_2_REG_H

#include "llvm/IR/PassManager.h"

struct PromotePass {
  public:
    PromotePass() {}
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "PromotePass"; }
};

#endif // MEM_2_REG_H
