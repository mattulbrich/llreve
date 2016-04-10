#pragma once

#include "MonoPair.h"
#include "Opts.h"
#include "SMT.h"

#include "clang/CodeGen/CodeGenAction.h"
#include "clang/Driver/Driver.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Option/Option.h"

auto main(int argc, const char **argv) -> int;

auto externDeclarations(llvm::Module &mod1, llvm::Module &mod2,
                        std::vector<smt::SharedSMTRef> &declarations,
                        uint8_t mem,
                        std::multimap<std::string, std::string> funCondMap)
    -> void;
auto funArgs(llvm::Function &fun, std::string prefix, uint32_t varArgs)
    -> std::vector<smt::SortedVar>;
auto getVarArgs(llvm::Function &fun) -> std::set<uint32_t>;
auto externFunDecl(llvm::Function &fun, int program, uint8_t mem)
    -> std::vector<smt::SharedSMTRef>;
auto doesNotRecurse(llvm::Function &fun) -> bool;
auto globalDeclarations(llvm::Module &mod1, llvm::Module &mod2)
    -> std::vector<smt::SharedSMTRef>;
auto globalDeclarationsForMod(int globalPointer, llvm::Module &mod,
                              llvm::Module &otherMod, int program)
    -> std::vector<smt::SharedSMTRef>;

auto doesAccessMemory(const llvm::Module &mod) -> bool;
