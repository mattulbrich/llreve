/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Compile.h"
#include "GitSHA1.h"
#include "ModuleSMTGeneration.h"
#include "Opts.h"
#include "Preprocess.h"
#include "Serialize.h"

#include "clang/Driver/Compilation.h"

#include "llvm/Support/ManagedStatic.h"

#include "llvm/Transforms/IPO.h"

using clang::CodeGenAction;

using clang::driver::ArgStringList;
using clang::driver::Command;
using clang::driver::Compilation;
using clang::driver::Driver;
using clang::driver::JobList;

using smt::SharedSMTRef;

using std::make_shared;
using std::placeholders::_1;
using std::set;
using std::shared_ptr;
using std::string;
using std::unique_ptr;
using std::vector;

using namespace llreve::opts;

// Input flags
static llreve::cl::list<string> IncludesFlag("I",
                                             llreve::cl::desc("Include path"),
                                             llreve::cl::cat(ReveCategory));
static llreve::cl::list<string> AssumeEquivalentFlags(
    "assume-equivalent",
    llreve::cl::desc("Pair of function names separated by ',' that are assumed "
                     "to be equivalent"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::list<string> CoupleFunctionsFlag(
    "couple-functions",
    llreve::cl::desc(
        "Pair of function names separated by ',' that are coupled"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<string> ResourceDirFlag(
    "resource-dir",
    llreve::cl::desc("Directory containing the clang resource files, "
                     "e.g. /usr/local/lib/clang/3.8.0"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<string> FileName1Flag(llreve::cl::Positional,
                                             llreve::cl::desc("FILE1"),
                                             llreve::cl::Required,
                                             llreve::cl::cat(ReveCategory));
static llreve::cl::opt<string> FileName2Flag(llreve::cl::Positional,
                                             llreve::cl::desc("FILE2"),
                                             llreve::cl::Required,
                                             llreve::cl::cat(ReveCategory));

// Serialize flags
static llreve::cl::opt<string>
    OutputFileNameFlag("o", llreve::cl::desc("SMT output filename"),
                       llreve::cl::value_desc("filename"),
                       llreve::cl::cat(ReveCategory));

// Preprocess flags
static llreve::cl::opt<bool> ShowCFGFlag("show-cfg",
                                         llreve::cl::desc("Show cfg"),
                                         llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool>
    ShowMarkedCFGFlag("show-marked-cfg",
                      llreve::cl::desc("Show cfg before mark removal"),
                      llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool> InferMarksFlag(
    "infer-marks",
    llreve::cl::desc("Infer marks instead of relying on annotations"),
    llreve::cl::cat(ReveCategory));

// SMT generation opts
static llreve::cl::opt<string> MainFunctionFlag(
    "fun", llreve::cl::desc("Name of the function which should be verified"),
    llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> HeapFlag("heap", llreve::cl::desc("Enable heap"),
                                      llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> StackFlag("stack",
                                       llreve::cl::desc("Enable stack"),
                                       llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool>
    GlobalConstantsFlag("strings", llreve::cl::desc("Set global constants"),
                        llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool>
    OnlyRecursiveFlag("only-rec",
                      llreve::cl::desc("Only generate recursive invariants"),
                      llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> NoByteHeapFlag(
    "no-byte-heap",
    llreve::cl::desc("Treat each primitive type as a single array entry"),
    llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> EverythingSignedFlag(
    "signed", llreve::cl::desc("Treat all operations as signed operatons"),
    llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool>
    MuZFlag("muz",
            llreve::cl::desc("Create smt intended for conversion to muz"),
            llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> PerfectSyncFlag(
    "perfect-sync",
    llreve::cl::desc("Perfect synchronization, don’t allow off by n loops"),
    llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool> PassInputThroughFlag(
    "pass-input-through",
    llreve::cl::desc("Pass the input arguments through the "
                     "complete program. This makes it possible "
                     "to use them in custom postconditions"),
    llreve::cl::cat(ReveCategory));

static llreve::cl::opt<bool>
    BitVectFlag("bitvect",
                llreve::cl::desc("Use bitvects instead of unbounded ints"),
                llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool>
    DontInstantiate("dont-instantiate",
                    llreve::cl::desc("Dont instantiate arrays"),
                    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool>
    InvertFlag("invert",
               llreve::cl::desc("Check for satisfiabilty of negation"),
               llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool> DisableAutoCouplingFlag(
    "disable-auto-coupling",
    llreve::cl::desc("Disable automatic coupling based on function names"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool> DisableAutoAbstraction(
    "disable-auto-abstraction",
    llreve::cl::desc(
        "Disable automatic abstraction of coupled extern functions "
        "as equivalent"),
    llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool>
    InitPredFlag("init-pred",
                 llreve::cl::desc("Introduce the toplevel predicate INIT"),
                 llreve::cl::cat(ReveCategory));
static llreve::cl::opt<bool> InlineLets("inline-lets",
                                        llreve::cl::desc("Inline lets"),
                                        llreve::cl::cat(ReveCategory));

static void printVersion() {
    std::cout << "llreve version " << g_GIT_SHA1 << "\n";
}
int main(int argc, const char **argv) {
    llreve::cl::SetVersionPrinter(printVersion);
    parseCommandLineArguments(argc, argv);

    PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag,
                                  InferMarksFlag);
    InputOpts inputOpts(IncludesFlag, ResourceDirFlag, FileName1Flag,
                        FileName2Flag);
    FileOptions fileOpts = getFileOptions(inputOpts.FileNames);
    SerializeOpts serializeOpts(OutputFileNameFlag, DontInstantiate,
                                BitVectFlag, true, InlineLets);

    MonoPair<shared_ptr<CodeGenAction>> acts =
        makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
                     make_shared<clang::EmitLLVMOnlyAction>());
    MonoPair<unique_ptr<llvm::Module>> modules =
        compileToModules(argv[0], inputOpts, acts);
    MonoPair<llvm::Module &> moduleRefs = {*modules.first, *modules.second};

    SMTGenerationOpts::initialize(
        findMainFunction(moduleRefs, MainFunctionFlag),
        HeapFlag ? Heap::Enabled : Heap::Disabled,
        StackFlag ? Stack::Enabled : Stack::Disabled,
        GlobalConstantsFlag ? GlobalConstants::Enabled
                            : GlobalConstants::Disabled,
        OnlyRecursiveFlag ? FunctionEncoding::OnlyRecursive
                          : FunctionEncoding::Iterative,
        NoByteHeapFlag ? ByteHeap::Disabled : ByteHeap::Enabled,
        EverythingSignedFlag, MuZFlag ? SMTFormat::Z3 : SMTFormat::SMTHorn,
        PerfectSyncFlag ? PerfectSynchronization::Enabled
                        : PerfectSynchronization::Disabled,
        PassInputThroughFlag, BitVectFlag, InvertFlag, InitPredFlag,
        DisableAutoAbstraction, {}, {}, {},
        addConstToFunctionPairSet(lookupFunctionNamePairs(
            moduleRefs, parseFunctionPairFlags(AssumeEquivalentFlags))),
        getCoupledFunctions(moduleRefs, DisableAutoCouplingFlag,
                            parseFunctionPairFlags(CoupleFunctionsFlag)),
        generateFunctionMap(moduleRefs));

    llvm::legacy::PassManager PM;
    PM.add(llvm::createStripSymbolsPass(true));
    PM.run(moduleRefs.first);
    PM.run(moduleRefs.second);

    const auto analysisResults = preprocessModules(moduleRefs, preprocessOpts);

    vector<SharedSMTRef> smtExprs =
        generateSMT(moduleRefs, analysisResults, fileOpts);

    serializeSMT(smtExprs,
                 SMTGenerationOpts::getInstance().OutputFormat == SMTFormat::Z3,
                 serializeOpts);

    llvm::llvm_shutdown();

    return 0;
}
