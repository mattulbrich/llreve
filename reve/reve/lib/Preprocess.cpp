#include "Preprocess.h"

#include "AnnotStackPass.h"
#include "CFGPrinter.h"
#include "ConstantProp.h"
#include "Helper.h"
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

#include "llvm/IR/Verifier.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/Scalar/ADCE.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"

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
        auto fam1 = preprocessFunction(*funPair.first, "1", opts);
        auto fam2 = preprocessFunction(*funPair.second, "2", opts);
        processedFuns.push_back(
            makeMonoPair(PreprocessedFunction(funPair.first, fam1),
                         PreprocessedFunction(funPair.second, fam2)));
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

shared_ptr<llvm::FunctionAnalysisManager>
preprocessFunction(llvm::Function &fun, string prefix, PreprocessOpts opts) {
    llvm::PassBuilder pb;
    auto fam =
        make_shared<llvm::FunctionAnalysisManager>(true); // enable debug log
    pb.registerFunctionAnalyses(*fam); // register basic analyses
    fam->registerPass(UnifyFunctionExitNodes());

    llvm::FunctionPassManager fpm(true); // enable debug log

    fpm.addPass(InlinePass());
    fpm.addPass(PromotePass()); // mem2reg
    fpm.addPass(llvm::SimplifyCFGPass());
    fpm.addPass(SplitEntryBlockPass());
    fam->registerPass(MarkAnalysis());
    fpm.addPass(RemoveMarkRefsPass());
    fpm.addPass(InstCombinePass());
    fpm.addPass(llvm::ADCEPass());
    fpm.addPass(ConstantProp());
    fam->registerPass(PathAnalysis());
    fpm.addPass(UniqueNamePass(prefix)); // prefix register names
    if (opts.ShowMarkedCFG) {
        fpm.addPass(CFGViewerPass()); // show marked cfg
    }
    fpm.addPass(RemoveMarkPass());
    if (opts.ShowCFG) {
        fpm.addPass(CFGViewerPass()); // show cfg
    }
    fpm.addPass(AnnotStackPass()); // annotate load/store of stack variables
    fpm.addPass(llvm::VerifierPass());
    // FPM.addPass(llvm::PrintFunctionPass(errs())); // dump function
    fpm.run(fun, fam.get());

    return fam;
}
