/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

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
