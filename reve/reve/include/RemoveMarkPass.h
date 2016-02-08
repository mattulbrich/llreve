#pragma once

#include "MarkAnalysis.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"

class RemoveMarkPass {
 public:
    static llvm::StringRef name() {
        return "RemoveMarkPass";
    }
    llvm::PreservedAnalyses run(llvm::Function &Fun, llvm::FunctionAnalysisManager *AM);
};
