#include "UniqueNamePass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

#include <iostream>

using llvm::PreservedAnalyses;
using llvm::StringRef;

PreservedAnalyses UniqueNamePass::run(llvm::Function &F,
                                      llvm::FunctionAnalysisManager *AM) {
    (void)AM;
    for (auto &Arg : F.args()) {
        makePrefixed(Arg, Prefix);
    }
    for (auto &Block : F) {
        for (auto &Inst : Block) {
            makePrefixed(Inst, Prefix);
        }
    }
    return PreservedAnalyses::none();
}

void makePrefixed(llvm::Value& Val, std::string Prefix) {
    // Note: The identity of values is not given by their names, so a
    // lot of register are simply unnamed. The numbers you see in the
    // output are only created when converting the assembly to a
    // string, so for most values, we simply set the complete name
    // here.
    Val.setName(Prefix + Val.getName());
}
