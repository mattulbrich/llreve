#pragma once

#include "MonoPair.h"
#include "Opts.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Support/ErrorOr.h"

struct PreprocessedFunction {
    llvm::Function *fun;
    std::shared_ptr<llvm::FunctionAnalysisManager> fam;
    PreprocessedFunction(llvm::Function *fun,
                         std::shared_ptr<llvm::FunctionAnalysisManager> fam)
        : fun(fun), fam(fam) {}
};

std::vector<MonoPair<PreprocessedFunction>>
preprocessFunctions(MonoPair<std::shared_ptr<llvm::Module>> modules,
                    PreprocessOpts opts);
auto zipFunctions(llvm::Module &mod1, llvm::Module &mod2)
    -> llvm::ErrorOr<std::vector<MonoPair<llvm::Function *>>>;
auto preprocessFunction(llvm::Function &fun, std::string prefix,
                        PreprocessOpts opts)
    -> std::shared_ptr<llvm::FunctionAnalysisManager>;
