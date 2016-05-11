#include <iostream>
#include <string>
#include <vector>

#include <sys/stat.h>

#include "Interpreter.h"
#include "SerializeTraces.h"

#include "Compat.h"
#include "Compile.h"
#include "Opts.h"
#include "Preprocess.h"

#include "clang/Driver/Compilation.h"

#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"

using std::string;
using std::vector;
using std::shared_ptr;
using std::make_shared;
using clang::CodeGenAction;

static llvm::cl::opt<string> FileName1Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE1"),
                                           llvm::cl::Required);
static llvm::cl::opt<string> FileName2Flag(llvm::cl::Positional,
                                           llvm::cl::desc("FILE2"),
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

static llvm::cl::opt<string> OutputDirectoryFlag(
    "output",
    llvm::cl::desc("Directory containing the output of the interpreter"),
    llvm::cl::Required);

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
    // Create directory
    int ret = mkdir(OutputDirectoryFlag.c_str(),
                    S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IWOTH);
    if (ret != 0) {
        if (errno != EEXIST) {
            logError("Couldn't create directory " + OutputDirectoryFlag + "\n");
            exit(1);
        }
    }
    serializeValuesInRange(
        makeMonoPair(modules.first->getFunction(MainFunctionFlag),
                     modules.second->getFunction(MainFunctionFlag)),
        -20, 20, OutputDirectoryFlag);
}
