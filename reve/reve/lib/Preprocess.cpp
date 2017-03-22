/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Preprocess.h"

#include "Helper.h"
#include "InferMarks.h"
#include "InlinePass.h"
#include "InlinePass.h"
#include "InstCombine.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "RemoveMarkPass.h"
#include "RemoveMarkRefsPass.h"
#include "SplitEntryBlockPass.h"
#include "UnifyFunctionExitNodes.h"
#include "UniqueNamePass.h"

#include "llvm/Analysis/CFGPrinter.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/Mem2Reg.h"

using std::map;
using std::vector;
using std::shared_ptr;
using std::make_shared;
using std::string;
using llvm::ErrorOr;

using namespace llreve::opts;

static void nameFunctionArguments(llvm::Function &fun, Program prog) {
    std::map<string, int> instructionNames;
    for (auto &arg : fun.args()) {
        makePrefixed(arg, std::to_string(programIndex(prog)), instructionNames);
    }
}

static void nameModuleGlobals(llvm::Module &module, Program prog) {
    for (auto &global : module.globals()) {
        global.setName(global.getName() + "$" +
                       std::to_string(programIndex(prog)));
    }
}

static void detectMemoryOptions(MonoPair<const llvm::Module &> modules) {
    if (doesAccessHeap(modules.first) || doesAccessHeap(modules.second)) {
        SMTGenerationOpts::getInstance().Heap = HeapOpt::Enabled;
    }
    if (doesAccessStack(modules.first) || doesAccessStack(modules.second)) {
        SMTGenerationOpts::getInstance().Stack = StackOpt::Enabled;
    }
}
AnalysisResultsMap preprocessModules(MonoPair<llvm::Module &> modules,
                                     PreprocessOpts opts) {
    map<const llvm::Function *, PassAnalysisResults> passResults;
    runFunctionPasses(modules.first, opts, passResults, Program::First);
    runFunctionPasses(modules.second, opts, passResults, Program::Second);
    nameModuleGlobals(modules.first, Program::First);
    nameModuleGlobals(modules.second, Program::Second);
    detectMemoryOptions(modules);
    AnalysisResultsMap analysisResults;
    runAnalyses(modules.first, Program::First, passResults, analysisResults);
    runAnalyses(modules.second, Program::Second, passResults, analysisResults);
    return analysisResults;
}

void runFunctionPasses(
    llvm::Module &module, PreprocessOpts opts,
    std::map<const llvm::Function *, PassAnalysisResults> &passResults,
    Program prog) {
    for (auto &f : module) {
        if (!f.isIntrinsic() && !isLlreveIntrinsic(f)) {
            if (hasFixedAbstraction(f)) {
                nameFunctionArguments(f, prog);
            } else {
                passResults.insert({&f, runFunctionPasses(f, prog, opts)});
            }
        }
    }
}

static llvm::ReturnInst *getReturnInstruction(llvm::Function &fun) {
    for (auto &bb : fun) {
        for (auto &inst : bb) {
            if (auto retInst = llvm::dyn_cast<llvm::ReturnInst>(&inst)) {
                return retInst;
            }
        }
    }
    assert(false);
    return nullptr;
}

PassAnalysisResults runFunctionPasses(llvm::Function &fun, Program prog,
                                      PreprocessOpts opts) {
    llvm::FunctionAnalysisManager fam(false);
    llvm::FunctionPassManager fpm(false);
    llvm::PassBuilder pb;
    pb.registerFunctionAnalyses(fam);
    fpm.addPass(UnifyFunctionExitNodes{});
    fam.registerPass([] { return FunctionExitNodeAnalysis(); });

    fpm.addPass(InlinePass{});
    fpm.addPass(llvm::PromotePass{});
    fpm.addPass(llvm::LoopSimplifyPass{});
    fpm.addPass(llvm::SimplifyCFGPass{});
    // TODO reenable
    // fpm->add(new SplitBlockPass());

    MarkAnalysis markAnalysis{};
    fam.registerPass([] { return InferMarksAnalysis(); });
    fam.registerPass([] { return MarkAnalysis{}; });
    if (!opts.InferMarks) {
        fpm.addPass(RemoveMarkRefsPass{});
    }
    fpm.addPass(InstCombinePass{});
    fpm.addPass(llvm::ADCEPass()); // supported
    // TODO reenable
    // fpm->add(llvm::createConstantPropagationPass());
    // // Passes need to have a default ctor
    UniqueNamePass::Prefix = std::to_string(programIndex(prog));
    fpm.addPass(UniqueNamePass{}); // prefix register names
    if (opts.ShowMarkedCFG) {
        fpm.addPass(llvm::CFGViewerPass()); // show marked cfg
    }
    if (!opts.InferMarks) {
        fpm.addPass(RemoveMarkPass{});
    }
    fam.registerPass([&] { return PathAnalysis(opts.InferMarks); });
    if (opts.ShowCFG) {
        fpm.addPass(llvm::CFGViewerPass{}); // show cfg
    }
    fpm.addPass(llvm::VerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    fpm.run(fun, fam);

    auto retInst = getReturnInstruction(fun);
    if (opts.InferMarks) {
        return {fam.getResult<InferMarksAnalysis>(fun),
                fam.getResult<PathAnalysis>(fun), retInst};
    } else {
        return {fam.getResult<MarkAnalysis>(fun),
                fam.getResult<PathAnalysis>(fun), retInst};
    }
}

void runAnalyses(const llvm::Module &module, Program prog,
                 map<const llvm::Function *, PassAnalysisResults> &passResults,
                 AnalysisResultsMap &analysisResults) {
    for (auto &f : module) {
        if (!f.isIntrinsic() && !isLlreveIntrinsic(f)) {
            if (!hasFixedAbstraction(f)) {
                analysisResults.insert({&f, runAnalyses(f, prog, passResults)});
            }
        }
    }
}

AnalysisResults runAnalyses(
    const llvm::Function &fun, Program prog,
    std::map<const llvm::Function *, PassAnalysisResults> &passResults) {
    const auto functionArguments = functionArgs(fun);
    const auto freeVariables =
        freeVars(passResults.at(&fun).paths, functionArguments, prog);
    return AnalysisResults(passResults.at(&fun).blockMarkMap,
                           passResults.at(&fun).paths, functionArguments,
                           freeVariables,
                           passResults.at(&fun).returnInstruction);
}

bool doesAccessHeap(const llvm::Module &mod) {
    for (auto &fun : mod) {
        if (!hasFixedAbstraction(fun)) {
            for (auto &bb : fun) {
                for (auto &instr : bb) {
                    if (llvm::isa<llvm::LoadInst>(&instr) ||
                        llvm::isa<llvm::StoreInst>(&instr)) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}

bool doesAccessStack(const llvm::Module &mod) {
    for (auto &fun : mod) {
        if (!hasFixedAbstraction(fun)) {
            for (auto &bb : fun) {
                for (auto &instr : bb) {
                    if (llvm::isa<llvm::AllocaInst>(&instr)) {
                        return true;
                    }
                }
            }
        }
    }
    return false;
}
