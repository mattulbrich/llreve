#ifndef UNIQUENAMEPASS_H
#define UNIQUENAMEPASS_H

#include "llvm/IR/PassManager.h"

class UniqueNamePass {
  public:
    explicit UniqueNamePass(const std::string Prefix) : Prefix(Prefix) {}
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static std::string name() { return "UniqueNamePass"; }

  private:
    const std::string Prefix;
};

void makePrefixed(llvm::Value& Val, std::string Prefix, std::map<std::string, int> &InstructionNames);

#endif // UNIQUENAMEPASS_H
