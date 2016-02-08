#pragma once

#include "llvm/IR/PassManager.h"

class AnnotStackPass {
  public:
    auto run(llvm::Function &F, llvm::FunctionAnalysisManager *AM)
        -> llvm::PreservedAnalyses;
    static auto name() -> llvm::StringRef { return "AnnotStackPass"; }
};

auto markStackInstruction(llvm::Instruction &Inst, std::string MetadataName,
                          int Pointer) -> void;
