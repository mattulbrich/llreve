#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/SlicingPass.h"

using std::make_shared;
using std::cout;
using std::endl;
using std::shared_ptr;
using std::string;
using clang::CodeGenAction;

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
	InputOpts inputOpts(Includes, ResourceDir, FileName,
		FileName);

	MonoPair<shared_ptr<CodeGenAction>> acts =
	makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
		make_shared<clang::EmitLLVMOnlyAction>());
	MonoPair<shared_ptr<llvm::Module>> modules =
		compileToModules(argv[0], inputOpts, acts);

	shared_ptr<llvm::Module> module = modules.first;

	for(llvm::Function& function:*module) {
		llvm::legacy::FunctionPassManager passManager(function.getParent());
		passManager.add(llvm::createPromoteMemoryToRegisterPass());		
	    passManager.add(llvm::createCFGSimplificationPass());
		passManager.run(function);
	}

	int i = 0;
	for(llvm::Function& function: *module) {
		for(llvm::BasicBlock& block: function) {
			for(llvm::Instruction& instruction: block) {			
				i++;
				if (i == 2) 
				{
					SlicingPass::toBeSliced(instruction);
				}
			}			
		}
	}

	llvm::legacy::PassManager PM;
	PM.add(new SlicingPass());
	PM.run(*module);

    printIR(*module);
    return 0;
}
