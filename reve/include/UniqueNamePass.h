#ifndef UNIQUENAMEPASS_H
#define UNIQUENAMEPASS_H

#include "llvm/IR/PassManager.h"

class UniqueNamePass {
  public:
    explicit UniqueNamePass(const llvm::StringRef Prefix_) : Prefix(Prefix_) {}
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "UniqueNamePass"; }

  private:
    const llvm::StringRef Prefix;
};

void makePrefixed(llvm::Value& Val, std::string Prefix);

#endif // UNIQUENAMEPASS_H
