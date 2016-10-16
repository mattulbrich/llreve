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

#include "CFGPrinter.h"
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
#include "UniqueNamePass.h"
#include "Unroll.h"

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

using std::map;
using std::vector;
using std::shared_ptr;
using std::make_shared;
using std::string;
using llvm::ErrorOr;

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

static void detectMemoryOptions(MonoPair<shared_ptr<llvm::Module>> modules) {
    if (doesAccessHeap(*modules.first) || doesAccessHeap(*modules.second)) {
        SMTGenerationOpts::getInstance().Heap = true;
    }
    if (doesAccessStack(*modules.first) || doesAccessStack(*modules.second)) {
        SMTGenerationOpts::getInstance().Stack = true;
    }
}
AnalysisResultsMap preprocessModules(MonoPair<shared_ptr<llvm::Module>> modules,
                                     PreprocessOpts opts) {
    map<const llvm::Function *, PassAnalysisResults> passResults;
    runFunctionPasses(*modules.first, opts, passResults, Program::First);
    runFunctionPasses(*modules.second, opts, passResults, Program::Second);
    nameModuleGlobals(*modules.first, Program::First);
    nameModuleGlobals(*modules.second, Program::Second);
    detectMemoryOptions(modules);
    AnalysisResultsMap analysisResults;
    runAnalyses(*modules.first, Program::First, passResults, analysisResults);
    runAnalyses(*modules.second, Program::Second, passResults, analysisResults);
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

PassAnalysisResults runFunctionPasses(llvm::Function &fun, Program prog,
                                      PreprocessOpts opts) {
    auto fpm =
        std::make_unique<llvm::legacy::FunctionPassManager>(fun.getParent());
    fpm->add(llvm::createUnifyFunctionExitNodesPass());

    fpm->add(new InlinePass());
    fpm->add(llvm::createPromoteMemoryToRegisterPass()); // mem2reg
    fpm->add(llvm::createLoopSimplifyPass());
    fpm->add(llvm::createCFGSimplificationPass());
    fpm->add(new SplitBlockPass());

    MarkAnalysis *markAnalysis = new MarkAnalysis();
    InferMarksAnalysis *inferMarkAnalysis = new InferMarksAnalysis();
    fpm->add(inferMarkAnalysis);
    fpm->add(markAnalysis);
    if (!opts.InferMarks) {
        fpm->add(new RemoveMarkRefsPass());
    }
    fpm->add(new InstCombinePass());
    fpm->add(llvm::createAggressiveDCEPass());
    fpm->add(llvm::createConstantPropagationPass());
    // Passes need to have a default ctor
    UniqueNamePass::Prefix = std::to_string(programIndex(prog));
    fpm->add(new UniqueNamePass()); // prefix register names
    if (opts.ShowMarkedCFG) {
        fpm->add(new CFGViewerPass()); // show marked cfg
    }
    if (!opts.InferMarks) {
        fpm->add(new RemoveMarkPass());
    }
    PathAnalysis *pathAnalysis = new PathAnalysis();
    pathAnalysis->InferMarks = opts.InferMarks;
    fpm->add(pathAnalysis);
    if (opts.ShowCFG) {
        fpm->add(new CFGViewerPass()); // show cfg
    }
    fpm->add(llvm::createVerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    fpm->doInitialization();
    fpm->run(fun);
    if (opts.InferMarks) {
        return {inferMarkAnalysis->BlockMarkMap, pathAnalysis->PathsMap};
    } else {
        return {markAnalysis->BlockMarkMap, pathAnalysis->PathsMap};
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
                           freeVariables);
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
