#pragma once

#include "Memory.h"
#include "MonoPair.h"
#include "Opts.h"
#include "Preprocess.h"
#include "SMT.h"

#include "llvm/IR/Module.h"

auto generateSMT(MonoPair<std::shared_ptr<llvm::Module>> modules,
                 std::vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
                 FileOptions fileOpts) -> std::vector<smt::SharedSMTRef>;
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
auto stringConstants(const llvm::Module &mod, std::string heap)
    -> std::vector<smt::SharedSMTRef>;
auto inInvariant(MonoPair<const llvm::Function *> funs, smt::SharedSMTRef body,
                 Memory memory, const llvm::Module &mod1,
                 const llvm::Module &mod2, bool strings, bool inInvariant)
    -> smt::SharedSMTRef;
auto outInvariant(MonoPair<std::vector<smt::SortedVar>> funArgs,
                  smt::SharedSMTRef body, Memory memory, const llvm::Type *type)
    -> smt::SharedSMTRef;
