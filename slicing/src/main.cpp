#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/PDGPass.h"
#include "core/SlicingPass.h"
#include "core/SyntacticSlicePass.h"
#include "core/Util.h"


#include "llvm/Transforms/Utils/Cloning.h"


#include "util/FileOperations.h"

using namespace std;

static llvm::cl::opt<std::string> FileName(llvm::cl::Positional,
	llvm::cl::desc("<input file>"),
	llvm::cl::Required);
static llvm::cl::list<string> Includes("I", llvm::cl::desc("Include path"),
	llvm::cl::cat(ReveCategory));
static llvm::cl::opt<string> ResourceDir(
	"resource-dir",
	llvm::cl::desc("Directory containing the clang resource files, "
		"e.g. /usr/local/lib/clang/3.8.0"),
	llvm::cl::cat(ReveCategory));

// Preprocess flags
static llvm::cl::opt<bool> ShowCFGFlag("show-cfg", llvm::cl::desc("Show cfg"),
	llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
ShowMarkedCFGFlag("show-marked-cfg",
	llvm::cl::desc("Show cfg before mark removal"),
	llvm::cl::cat(ReveCategory));


void printIR(llvm::Function& function) {
	llvm::legacy::FunctionPassManager PM(function.getParent());
	PM.add(llvm::createPrintFunctionPass(llvm::outs()));
	PM.run(function);
}

void printIR(llvm::Module& module) {
	//for(llvm::Function& function:module) {
		//cout << function.getName().str() << endl;
	//	printIR(function);
	//}

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPrintModulePass(llvm::outs()));
	PM.run(module);
}

int main(int argc, const char **argv) {
	llvm::cl::ParseCommandLineOptions(argc, argv);

	shared_ptr<llvm::Module> program = getModuleFromFile(FileName, ResourceDir, Includes);
	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);

	return 0;
}
