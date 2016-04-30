#include "Preprocess.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "Helper.h"
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

using std::vector;
using std::shared_ptr;
using std::make_shared;
using std::string;
using llvm::ErrorOr;

vector<MonoPair<PreprocessedFunction>>
preprocessFunctions(MonoPair<shared_ptr<llvm::Module>> modules,
                    PreprocessOpts opts) {
    vector<MonoPair<PreprocessedFunction>> processedFuns;
    auto funs = zipFunctions(*modules.first, *modules.second);
    for (auto funPair : funs.get()) {
        auto results1 = preprocessFunction(*funPair.first, "1", opts);
        auto results2 = preprocessFunction(*funPair.second, "2", opts);
        processedFuns.push_back(
            makeMonoPair(PreprocessedFunction(funPair.first, results1),
                         PreprocessedFunction(funPair.second, results2)));
    }
    return processedFuns;
}

ErrorOr<std::vector<MonoPair<llvm::Function *>>>
zipFunctions(llvm::Module &mod1, llvm::Module &mod2) {
    std::vector<MonoPair<llvm::Function *>> funs;
    int size1 = 0;
    int size2 = 0;
    for (auto &fun : mod1) {
        if (!fun.isDeclaration()) {
            ++size1;
        }
    }
    for (auto &fun : mod2) {
        if (!fun.isDeclaration()) {
            ++size2;
        }
    }
    if (size1 != size2) {
        logWarning("Number of functions is not equal\n");
    }
    for (auto &Fun1 : mod1) {
        if (Fun1.isDeclaration()) {
            continue;
        }
        llvm::Function *fun2 = mod2.getFunction(Fun1.getName());
        if (!fun2) {
            logWarning("No corresponding function for " + Fun1.getName() +
                       "\n");
            continue;
        }
        llvm::Function *fun1 = &Fun1;
        funs.push_back(makeMonoPair(fun1, fun2));
    }
    return ErrorOr<std::vector<MonoPair<llvm::Function *>>>(funs);
}

AnalysisResults preprocessFunction(llvm::Function &fun, string prefix,
                                   PreprocessOpts opts) {
    auto fpm =
        llvm::make_unique<llvm::legacy::FunctionPassManager>(fun.getParent());
    fpm->add(llvm::createUnifyFunctionExitNodesPass());

    fpm->add(new InlinePass());
    fpm->add(llvm::createPromoteMemoryToRegisterPass()); // mem2reg
    fpm->add(llvm::createCFGSimplificationPass());
    fpm->add(new SplitEntryBlockPass());
    MarkAnalysis *markAnalysis = new MarkAnalysis();
    fpm->add(markAnalysis);
    fpm->add(new RemoveMarkRefsPass());
    fpm->add(new InstCombinePass());
    fpm->add(llvm::createAggressiveDCEPass());
    fpm->add(llvm::createConstantPropagationPass());
    PathAnalysis *pathAnalysis = new PathAnalysis();
    fpm->add(pathAnalysis);
    // Passes need to have a default ctor
    UniqueNamePass::Prefix = prefix;
    fpm->add(new UniqueNamePass()); // prefix register names
    if (opts.ShowMarkedCFG) {
        fpm->add(new CFGViewerPass()); // show marked cfg
    }
    fpm->add(new RemoveMarkPass());
    if (opts.ShowCFG) {
        fpm->add(new CFGViewerPass()); // show cfg
    }
    fpm->add(new AnnotStackPass()); // annotate load/store of stack variables
    llvm::LoopInfoWrapperPass *loopInfo = new llvm::LoopInfoWrapperPass();
    fpm->add(loopInfo);
    fpm->add(llvm::createVerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    fpm->doInitialization();
    fpm->run(fun);

    if(prefix == "2") {
        unrollAtMark(fun, 42, markAnalysis->BlockMarkMap);
        fun.viewCFG();
        fun.print(llvm::errs());
        llvm::verifyFunction(fun, &llvm::errs());
    }
    return AnalysisResults(markAnalysis->BlockMarkMap, pathAnalysis->PathsMap,
                           loopInfo);
}
