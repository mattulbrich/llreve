#include <iostream>
#include <string>
#include <vector>

#include "Interpreter.h"

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

int main(int argc, const char **argv) {
    llvm::cl::ParseCommandLineOptions(argc, argv);
    InputOpts inputOpts(IncludesFlag, ResourceDirFlag, FileName1Flag,
                        FileName2Flag);
    PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag);

    MonoPair<shared_ptr<CodeGenAction>> acts =
        makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
                     make_shared<clang::EmitLLVMOnlyAction>());
    MonoPair<shared_ptr<llvm::Module>> modules =
        compileToModules(argv[0], inputOpts, acts);
    vector<MonoPair<PreprocessedFunction>> preprocessedFuns =
        preprocessFunctions(modules, preprocessOpts);
    VarMap variables;
    // variables["dest$1_0"] = make_shared<VarInt>(0);
    // variables["src$1_0"] = make_shared<VarInt>(16);
    // variables["size$1_0"] = make_shared<VarInt>(4);
    variables["i$1_0"] = make_shared<VarInt>(3);
    variables["j$1_0"] = make_shared<VarInt>(5);
    Heap heap;
    // heap[16] = VarInt(4);
    // heap[20] = VarInt(3);
    // heap[24] = VarInt(2);
    // heap[28] = VarInt(1);
    State entry(variables, heap);
    Call call = interpretFunction(*modules.first->getFunction(MainFunctionFlag), entry);
    std::cout << call.toJSON().dump(4) << std::endl;
}
