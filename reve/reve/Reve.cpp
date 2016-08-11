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

// Input flags
static llvm::cl::list<string> IncludesFlag("I", llvm::cl::desc("Include path"),
                                           llvm::cl::cat(ReveCategory));
static llvm::cl::opt<string> ResourceDirFlag(
    "resource-dir",
    llvm::cl::desc("Directory containing the clang resource files, "
                   "e.g. /usr/local/lib/clang/3.8.0"),
    llvm::cl::cat(ReveCategory));
static llvm::cl::opt<string> FileName1Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE1"),
                                           llvm::cl::Required,
                                           llvm::cl::cat(ReveCategory));
static llvm::cl::opt<string> FileName2Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE2"),
                                           llvm::cl::Required,
                                           llvm::cl::cat(ReveCategory));

// Serialize flags
static llvm::cl::opt<string>
    OutputFileNameFlag("o", llvm::cl::desc("SMT output filename"),
                       llvm::cl::value_desc("filename"),
                       llvm::cl::cat(ReveCategory));

// Preprocess flags
static llvm::cl::opt<bool> ShowCFGFlag("show-cfg", llvm::cl::desc("Show cfg"),
                                       llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
    ShowMarkedCFGFlag("show-marked-cfg",
                      llvm::cl::desc("Show cfg before mark removal"),
                      llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool> InferMarksFlag(
    "infer-marks",
    llvm::cl::desc("Infer marks instead of relying on annotations"),
    llvm::cl::cat(ReveCategory));

// SMT generation opts
static llvm::cl::opt<string> MainFunctionFlag(
    "fun", llvm::cl::desc("Name of the function which should be verified"),
    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> HeapFlag("heap", llvm::cl::desc("Enable heap"),
                                    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> StackFlag("stack", llvm::cl::desc("Enable stack"),
                                     llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool>
    GlobalConstantsFlag("strings", llvm::cl::desc("Set global constants"),
                        llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool>
    OnlyRecursiveFlag("only-rec",
                      llvm::cl::desc("Only generate recursive invariants"),
                      llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> NoByteHeapFlag(
    "no-byte-heap",
    llvm::cl::desc("Treat each primitive type as a single array entry"),
    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> EverythingSignedFlag(
    "signed", llvm::cl::desc("Treat all operations as signed operatons"),
    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> SingleInvariantFlag(
    "single-invariant",
    llvm::cl::desc("Use a single invariant indexed by the mark"),
    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool>
    MuZFlag("muz", llvm::cl::desc("Create smt intended for conversion to muz"),
            llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> PerfectSyncFlag(
    "perfect-sync",
    llvm::cl::desc("Perfect synchronization, don’t allow off by n loops"),
    llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool>
    NestFlag("nest",
             llvm::cl::desc("Nest clauses, this can sometimes help eldarica"),
             llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool> PassInputThroughFlag(
    "pass-input-through",
    llvm::cl::desc("Pass the input arguments through the "
                   "complete program. This makes it possible "
                   "to use them in custom postconditions"),
    llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
    BitVectFlag("bitvect",
                llvm::cl::desc("Use bitvects instead of unbounded ints"),
                llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
    DontInstantiate("dont-instantiate",
                    llvm::cl::desc("Dont instantiate arrays"),
                    llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
    InvertFlag("invert", llvm::cl::desc("Check for satisfiabilty of negation"),
               llvm::cl::cat(ReveCategory));

static llvm::cl::opt<bool>
    InitPredFlag("init-pred", llvm::cl::desc("Introduce the toplevel predicate INIT"),
               llvm::cl::cat(ReveCategory));
int main(int argc, const char **argv) {
    parseCommandLineArguments(argc, argv);

    PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag,
                                  InferMarksFlag);
    SMTGenerationOpts::initialize(
        MainFunctionFlag, HeapFlag, StackFlag, GlobalConstantsFlag,
        OnlyRecursiveFlag, NoByteHeapFlag, EverythingSignedFlag,
        SingleInvariantFlag, MuZFlag, PerfectSyncFlag, NestFlag,
        PassInputThroughFlag, BitVectFlag, InvertFlag, InitPredFlag, {});
    InputOpts inputOpts(IncludesFlag, ResourceDirFlag, FileName1Flag,
                        FileName2Flag);
    FileOptions fileOpts = getFileOptions(inputOpts.FileNames);
    SerializeOpts serializeOpts(OutputFileNameFlag, DontInstantiate, false,
                                BitVectFlag, true);

    MonoPair<shared_ptr<CodeGenAction>> acts =
        makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
                     make_shared<clang::EmitLLVMOnlyAction>());
    MonoPair<shared_ptr<llvm::Module>> modules =
        compileToModules(argv[0], inputOpts, acts);

    llvm::legacy::PassManager PM;
    PM.add(llvm::createStripSymbolsPass(true));
    PM.run(*modules.first);
    PM.run(*modules.second);

    vector<MonoPair<PreprocessedFunction>> preprocessedFuns =
        preprocessFunctions(modules, preprocessOpts);

    vector<SharedSMTRef> smtExprs =
        generateSMT(modules, preprocessedFuns, fileOpts);

    serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);

    llvm::llvm_shutdown();

    return 0;
}
