#pragma once

#include <map>

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Value.h"

class UniqueNamePass : public llvm::FunctionPass {
  public:
    explicit UniqueNamePass() : llvm::FunctionPass(ID) {}
    bool runOnFunction(llvm::Function &F) override;
    static llvm::StringRef name() { return "UniqueNamePass"; }
    static char ID;
    // I haven’t figured out how to pass parameters to a pass
    static std::string Prefix;
    void getAnalysisUsage(llvm::AnalysisUsage& AU) const override;
};

void makePrefixed(llvm::Value &Val, std::string Prefix,
                  std::map<std::string, int> &InstructionNames);
