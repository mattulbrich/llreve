#ifndef UNIQUE_NAME_PASS_H
#define UNIQUE_NAME_PASS_H

#include "llvm/IR/PassManager.h"

class UniqueNamePass {
  public:
    UniqueNamePass(const llvm::StringRef Prefix_) : Prefix(Prefix_) {}
    llvm::PreservedAnalyses run(llvm::Function &F,
                                llvm::FunctionAnalysisManager *AM);
    static llvm::StringRef name() { return "UniqueNamePass"; }

  private:
    const llvm::StringRef Prefix;
};

const std::string rename(std::string Name, std::string Prefix);
void makePrefixed(llvm::Value Val, std::string Prefix);

#endif // UNIQUE_NAME_PASS_H
