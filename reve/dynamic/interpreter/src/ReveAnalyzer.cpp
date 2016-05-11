#include <iostream>
#include <string>
#include <vector>

#include "Analysis.h"
#include "Compat.h"
#include "Compile.h"
#include "ModuleSMTGeneration.h"
#include "Opts.h"
#include "Preprocess.h"
#include "Serialize.h"
#include "SerializeTraces.h"

#include "clang/Driver/Compilation.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"

using std::string;
using std::vector;
using std::shared_ptr;
using std::make_shared;
using std::map;

using clang::CodeGenAction;

static llvm::cl::opt<string> FileName1Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE1"),
                                           llvm::cl::Required);
static llvm::cl::opt<string> FileName2Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE2"),
                                           llvm::cl::Required);
static llvm::cl::opt<string> OutputDirectoryFlag(
    "output",
    llvm::cl::desc("Directory containing the output of the interpreter"),
    llvm::cl::Required);
static llvm::cl::list<string> IncludesFlag("I", llvm::cl::desc("Include path"));
static llvm::cl::opt<string> ResourceDirFlag(
    "resource-dir",
    llvm::cl::desc("Directory containing the clang resource files, "
                   "e.g. /usr/local/lib/clang/3.8.0"));

static llvm::cl::opt<bool> ShowCFGFlag("show-cfg", llvm::cl::desc("Show cfg"));
static llvm::cl::opt<bool>
    ShowMarkedCFGFlag("show-marked-cfg",
                      llvm::cl::desc("Show cfg before mark removal"));

static llvm::cl::opt<string> MainFunctionFlag(
    "fun", llvm::cl::desc("Name of the function which should be verified"),
    llvm::cl::Required);
// Serialize flags
static llvm::cl::opt<string>
    OutputFileNameFlag("o", llvm::cl::desc("SMT output filename"),
                       llvm::cl::value_desc("filename"), llvm::cl::Required);

int main(int argc, const char **argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv);
    InputOpts inputOpts(IncludesFlag, ResourceDirFlag, FileName1Flag,
                        FileName2Flag);
    PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag, false);

    MonoPair<shared_ptr<CodeGenAction>> acts =
        makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
                     make_shared<clang::EmitLLVMOnlyAction>());
    MonoPair<shared_ptr<llvm::Module>> modules =
        compileToModules(argv[0], inputOpts, acts);
    vector<MonoPair<PreprocessedFunction>> preprocessedFuns =
        preprocessFunctions(modules, preprocessOpts);
    vector<smt::SharedSMTRef> smtExprs = driver(
        modules, OutputDirectoryFlag, preprocessedFuns, MainFunctionFlag);
    // map<int, smt::SharedSMTRef> invariantDefinitions =
    //     analyse(OutputDirectoryFlag, preprocessedFuns, MainFunctionFlag);
    // SMTGenerationOpts::initialize(MainFunctionFlag, false, false, false,
    // false,
    //                               false, false, false, false, false, false,
    //                               false, invariantDefinitions);
    // vector<smt::SharedSMTRef> smtExprs = generateSMT(
    //     modules, preprocessedFuns, FileOptions({}, nullptr, nullptr, false));
    serializeSMT(smtExprs, false, SerializeOpts(OutputFileNameFlag));

    llvm::llvm_shutdown();
}
