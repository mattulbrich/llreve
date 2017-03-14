#pragma once

#include <llvm/IR/PassManager.h>

class UnifyFunctionExitNodes
    : public llvm::PassInfoMixin<UnifyFunctionExitNodes> {
  public:
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager &am);
};

struct ExitNode {
    llvm::BasicBlock *returnBlock;
};
class FunctionExitNodeAnalysis
    : public llvm::AnalysisInfoMixin<FunctionExitNodeAnalysis> {
  public:
    using Result = ExitNode;
    Result run(llvm::Function &fun, llvm::FunctionAnalysisManager &am);

  private:
    friend llvm::AnalysisInfoMixin<FunctionExitNodeAnalysis>;
    static llvm::AnalysisKey Key;
};
