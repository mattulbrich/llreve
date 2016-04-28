#pragma once

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Instruction.h"

class AnnotStackPass : public llvm::FunctionPass {
  public:
    bool runOnFunction(llvm::Function &F) override;
    static auto name() -> llvm::StringRef { return "AnnotStackPass"; }
    AnnotStackPass() : llvm::FunctionPass(ID) {}
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
    static char ID;
};

auto markStackInstruction(llvm::Instruction &Inst, std::string MetadataName,
                          int Pointer) -> void;
