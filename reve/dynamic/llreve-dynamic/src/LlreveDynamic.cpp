/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include <iostream>
#include <string>
#include <vector>

#include "Compat.h"
#include "Compile.h"
#include "GitSHA1.h"
#include "ModuleSMTGeneration.h"
#include "Opts.h"
#include "Preprocess.h"
#include "Serialize.h"
#include "llreve/dynamic/Analysis.h"
#include "llreve/dynamic/Model.h"
#include "llreve/dynamic/SerializeTraces.h"

#include "clang/Driver/Compilation.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Transforms/IPO.h"

#include <sys/stat.h>

using std::string;
using std::vector;
using std::shared_ptr;
using std::make_shared;
using std::map;

using clang::CodeGenAction;

using namespace llreve::dynamic;
using namespace llreve::opts;

static llreve::cl::opt<string> FileName1Flag(llreve::cl::Positional,
                                             llreve::cl::desc("FILE1"),
                                             llreve::cl::Required);
static llreve::cl::opt<string> FileName2Flag(llreve::cl::Positional,
                                             llreve::cl::desc("FILE2"),
                                             llreve::cl::Required);
static llreve::cl::opt<bool> // The parser
    BoundedFlag("bounded", llreve::cl::desc("Use bounded integers"));
static llreve::cl::opt<bool> HeapFlag("heap",
                                      llreve::cl::desc("Activate heap"));
static llreve::cl::opt<bool>
    InstantiateFlag("instantiate", llreve::cl::desc("Instantiate arrays"));
static llreve::cl::opt<string>
    PatternFileFlag("patterns",
                    llreve::cl::desc("Path to file containing patterns"),
                    llreve::cl::Required);
static llreve::cl::list<string> IncludesFlag("I",
                                             llreve::cl::desc("Include path"));
static llreve::cl::opt<string> ResourceDirFlag(
    "resource-dir",
    llreve::cl::desc("Directory containing the clang resource files, "
                     "e.g. /usr/local/lib/clang/3.8.0"));

static llreve::cl::opt<bool> ShowCFGFlag("show-cfg",
                                         llreve::cl::desc("Show cfg"));
static llreve::cl::opt<bool>
    ShowMarkedCFGFlag("show-marked-cfg",
                      llreve::cl::desc("Show cfg before mark removal"));

static llreve::cl::opt<string> MainFunctionFlag(
    "fun", llreve::cl::desc("Name of the function which should be verified"));
// Serialize flags
static llreve::cl::opt<string>
    OutputFileNameFlag("o", llreve::cl::desc("SMT output filename"),
                       llreve::cl::value_desc("filename"));
static llreve::cl::opt<bool> EverythingSignedFlag(
    "signed", llreve::cl::desc("Treat all operations as signed operatons"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool>
    MergeImplications("merge-implications",
                      llreve::cl::desc("Merge implications"));
static llreve::cl::opt<bool>
    OnlyTransform("only-transform",
                  llreve::cl::desc("Only infer unroll and peel factors"));

static void printVersion() {
    std::cout << "llreve-dynamic version " << g_GIT_SHA1 << "\n";
}

int main(int argc, const char **argv) {
    llreve::cl::SetVersionPrinter(printVersion);
    llreve::cl::ParseCommandLineOptions(argc, argv);
    InputOpts inputOpts(IncludesFlag, ResourceDirFlag, FileName1Flag,
                        FileName2Flag);
    PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag, false);

    std::unique_ptr<CodeGenAction> act1 =
        std::make_unique<clang::EmitLLVMOnlyAction>();
    std::unique_ptr<CodeGenAction> act2 =
        std::make_unique<clang::EmitLLVMOnlyAction>();
    MonoPair<shared_ptr<llvm::Module>> modules =
        compileToModules(argv[0], inputOpts, {*act1, *act2});
    llvm::legacy::PassManager PM;
    PM.add(llvm::createStripSymbolsPass(true));
    PM.run(*modules.first);
    PM.run(*modules.second);
    MonoPair<llvm::Module &> moduleRefs = {*modules.first, *modules.second};

    std::map<const llvm::Function *, int> functionNumerals;
    MonoPair<std::map<int, const llvm::Function *>> reversedFunctionNumerals = {
        {}, {}};
    std::tie(functionNumerals, reversedFunctionNumerals) =
        generateFunctionMap(moduleRefs);

    SMTGenerationOpts::initialize(
        findMainFunction(moduleRefs, MainFunctionFlag),
        HeapFlag ? llreve::opts::HeapOpt::Enabled
                 : llreve::opts::HeapOpt::Disabled,
        StackOpt::Disabled, GlobalConstantsOpt::Disabled,
        FunctionEncoding::Iterative, ByteHeapOpt::Enabled, EverythingSignedFlag,
        OnlyTransform ? SMTFormat::Z3 : SMTFormat::SMTHorn,
        PerfectSynchronization::Disabled, false, BoundedFlag, !OnlyTransform,
        false, false, {}, {}, {}, {}, inferCoupledFunctionsByName(moduleRefs),
        functionNumerals, reversedFunctionNumerals);

    AnalysisResultsMap analysisResults =
        preprocessModules(moduleRefs, preprocessOpts);
    // fopen doesn’t signal if the path points to a directory, thus we have to
    // check for that separately and to catch the error.
    struct stat s;
    int ret = stat(PatternFileFlag.c_str(), &s);
    if (ret != 0) {
        logError("Couldn’t open pattern file\n");
        exit(1);
    }
    if (s.st_mode & S_IFDIR) {
        logError("Pattern file points to a directory\n");
        exit(1);
    }

    FILE *patternFile = fopen(PatternFileFlag.c_str(), "r");
    if (patternFile == nullptr) {
        logError("Couldn’t open pattern file\n");
        exit(1);
    }
    auto patterns = parsePatterns(patternFile);
    std::cerr << "Found " << patterns.size() << " patterns\n";
    for (auto pat : patterns) {
        pat->dump(std::cerr);
        std::cerr << "\n";
    }
    fclose(patternFile);

    FileOptions fileOpts = getFileOptions(inputOpts.FileNames);
    vector<smt::SharedSMTRef> smtExprs;
    if (OnlyTransform) {
        smtExprs = driver(moduleRefs, analysisResults, patterns, fileOpts);
    } else {
        smtExprs = cegarDriver(moduleRefs, analysisResults, patterns, fileOpts);
    }
    if (!smtExprs.empty() && !OutputFileNameFlag.empty()) {
        serializeSMT(smtExprs, OnlyTransform,
                     SerializeOpts(OutputFileNameFlag, !InstantiateFlag,
                                   MergeImplications, true, false));
    }

    llvm::llvm_shutdown();
}
