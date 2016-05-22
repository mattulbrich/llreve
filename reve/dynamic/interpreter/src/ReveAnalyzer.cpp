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
#include "llvm/Transforms/IPO.h"

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
static llvm::cl::opt<string>
    PatternFileFlag("patterns",
                    llvm::cl::desc("Path to file containing patterns"),
                    llvm::cl::Required);
static llvm::cl::opt<string> OutputDirectoryFlag(
    "output",
    llvm::cl::desc("Directory containing the output of the interpreter"));
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
	llvm::legacy::PassManager PM;
	PM.add(llvm::createStripSymbolsPass(true));
	PM.run(*modules.first);
	PM.run(*modules.second);
    vector<MonoPair<PreprocessedFunction>> preprocessedFuns =
        preprocessFunctions(modules, preprocessOpts);
    FILE* patternFile = fopen(PatternFileFlag.c_str(), "r");
    auto patterns = parsePatterns(patternFile);
    std::cerr << "Found " << patterns.size() << " patterns\n";
    for (auto pat : patterns) {
        pat->dump(std::cerr);
        std::cerr << "\n";
    }
    fclose(patternFile);
    vector<smt::SharedSMTRef> smtExprs =
        driver(modules, preprocessedFuns, MainFunctionFlag, patterns);

    serializeSMT(smtExprs, false, SerializeOpts(OutputFileNameFlag, !InstantiateStorage));

    llvm::llvm_shutdown();
}
