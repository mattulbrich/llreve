#include <iostream>

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

#include "UniqueNamePass.h"

using llvm::PreservedAnalyses;
using llvm::StringRef;

PreservedAnalyses UniqueNamePass::run(llvm::Function &F,
                                      llvm::FunctionAnalysisManager *AM) {
    (void)AM;
    for (auto &Arg : F.args()) {
        Arg.setName(rename(Arg.getName(), Prefix));
    }
    for (auto &Block : F) {
        for (auto &Inst : Block) {
            Inst.setName(rename(Inst.getName(), Prefix));
        }
    }
    return PreservedAnalyses::none();
}

const std::string rename(std::string Name, std::string Prefix) {
    return Prefix + Name;
}

void makePrefixed(llvm::Value Val, std::string Prefix) {
    Val.setName(rename(Val.getName(), Prefix));
}
