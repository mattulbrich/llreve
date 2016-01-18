#pragma once

#include "llvm/IR/PassManager.h"

class UniqueNamePass {
  public:
    explicit UniqueNamePass(const std::string Prefix) : Prefix(Prefix) {}
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "UniqueNamePass"; }

  private:
    const std::string Prefix;
};

void makePrefixed(llvm::Value& Val, std::string Prefix, std::map<std::string, int> &InstructionNames);
