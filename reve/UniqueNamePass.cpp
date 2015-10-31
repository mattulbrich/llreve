#include "UniqueNamePass.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"

#include <iostream>
#include <map>

using llvm::PreservedAnalyses;
using llvm::StringRef;

PreservedAnalyses UniqueNamePass::run(llvm::Function &F,
                                      llvm::FunctionAnalysisManager *AM) {
    (void)AM;
    std::map<StringRef, int> InstructionNames;

    for (auto &Args : F.args()) {
        makePrefixed(Args, Prefix, InstructionNames);
    }

    for (auto &Block : F) {
        for (auto &Inst : Block) {
            makePrefixed(Inst, Prefix, InstructionNames);
        }
    }
    return PreservedAnalyses::none();
}

void makePrefixed(llvm::Value &Val, std::string Prefix,
                  std::map<StringRef, int> &InstructionNames) {
    // Note: The identity of values is not given by their names, so a
    // lot of register are simply unnamed. The numbers you see in the
    // output are only created when converting the assembly to a
    // string, so for most values, we simply set the complete name
    // here.

    // It is illegal to specify names for void instructions
    if (!Val.getType()->isVoidTy()) {
        StringRef OldName = Val.getName();
        if (OldName == "") {
            OldName = "_"; // Make valid name for smt solvers
        }
        if (InstructionNames.find(OldName) == InstructionNames.end()) {
            InstructionNames.insert(std::make_pair(OldName, 0));
        }
        Val.setName(OldName + "$" + Prefix + "_" +
                    std::to_string(InstructionNames.at(OldName)++));
    }
}
