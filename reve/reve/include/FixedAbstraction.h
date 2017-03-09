#pragma once

#include "Program.h"
#include "SMT.h"

#include "llvm/IR/Module.h"

auto getVarArgs(const llvm::Function &fun) -> std::set<uint32_t>;
auto externDeclarations(const llvm::Module &mod1, const llvm::Module &mod2,
                        std::vector<smt::SharedSMTRef> &declarations,
                        std::multimap<std::string, std::string> funCondMap)
    -> void;
auto externFunDecl(const llvm::Function &fun, Program program)
    -> std::vector<std::unique_ptr<smt::SMTExpr>>;
auto equivalentExternDecls(const llvm::Function &fun1,
                           const llvm::Function &fun2,
                           std::multimap<std::string, std::string> funCondMap)
    -> std::vector<std::unique_ptr<smt::SMTExpr>>;
auto notEquivalentExternDecls(const llvm::Function &fun1,
                              const llvm::Function &fun2)
    -> std::vector<std::unique_ptr<smt::SMTExpr>>;
