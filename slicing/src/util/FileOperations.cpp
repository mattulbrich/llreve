#include "FileOperations.h"

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
//#include "llvm/IR/IRPrintingPasses.h"
//#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "core/AddVariableNamePass.h"
#include "llvm/Transforms/IPO.h"

#include "llvm/Transforms/Utils/Cloning.h"


using namespace std;
using namespace llvm;
using namespace clang;

shared_ptr<llvm::Module> getModuleFromFile(string fileName, string resourceDir, vector<std::string> includes){
	// The CodeGenAction does need an LLVMContext. If none is provided, than
	// it will create its own AND delet it on destructor. This would render
	// the produced module unusable. Therefore we need an LLVMContext, which
	// exists during the hole lifetime of the program. (Comparable to Singleton)
	// Note: This may cause trubble, if we start multi threading!
	static llvm::LLVMContext context;

	InputOpts inputOpts(includes, resourceDir, fileName, fileName);

	MonoPair<shared_ptr<CodeGenAction>> acts =
	makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(&context),
		make_shared<clang::EmitLLVMOnlyAction>(&context));

	MonoPair<shared_ptr<llvm::Module>> modules =
	compileToModules("", inputOpts, acts);
	shared_ptr<llvm::Module> program = modules.first;

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPromoteMemoryToRegisterPass());
	PM.add(new AddVariableNamePass());
	PM.add(llvm::createStripSymbolsPass(true));
	PM.run(*program);

	shared_ptr<llvm::Module> sliceCandidate = CloneModule(&*program);
	return program;
}
