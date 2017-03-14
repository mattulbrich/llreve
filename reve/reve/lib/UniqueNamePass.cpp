/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "UniqueNamePass.h"

#include "PathAnalysis.h"

#include <iostream>

#include "llvm/IR/Function.h"

using std::string;

llvm::PreservedAnalyses UniqueNamePass::run(llvm::Function &F,
                                            llvm::FunctionAnalysisManager &am) {
    std::map<string, int> InstructionNames;
    std::string funName = F.getName();

    for (auto &Arg : F.args()) {
        makePrefixed(Arg, Prefix, InstructionNames);
    }

    int i = 0;
    for (auto &Block : F) {
        Block.setName(funName + "/" + std::to_string(i) + "$" + Prefix);
        ++i;
        for (auto &Inst : Block) {
            makePrefixed(Inst, Prefix, InstructionNames);
        }
    }
    return llvm::PreservedAnalyses::all();
}

void makePrefixed(llvm::Value &Val, std::string Prefix,
                  std::map<string, int> &InstructionNames) {
    // Note: The identity of values is not given by their names, so a
    // lot of register are simply unnamed. The numbers you see in the
    // output are only created when converting the assembly to a
    // string, so for most values, we simply set the complete name
    // here.

    // It is illegal to specify names for void instructions
    if (!Val.getType()->isVoidTy()) {
        string OldName = Val.getName();
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

string UniqueNamePass::Prefix = "ERROR";
