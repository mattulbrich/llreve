#include "catch.hpp"

#include "preprocessing/ExplicitAssignPass.h"
#include "preprocessing/StripExplicitAssignPass.h"
#include "preprocessing/PromoteAssertSlicedPass.h"
#include "preprocessing/AddVariableNamePass.h"

#include "util/FileOperations.h"

#include "Opts.h"
#include "Compile.h"
#include "Helper.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"

using namespace std;
using namespace llvm;
using namespace clang;

TEST_CASE("TestForceAssignPass", "[Pass]") {
	static llvm::LLVMContext context;
	string fileName = "../testdata/benchmarks/informationflow_dynamic_override.c";
	string resourceDir = "";
	vector<std::string> includes;
	InputOpts inputOpts(includes, resourceDir, fileName, fileName);

	MonoPair<shared_ptr<CodeGenAction>> acts =
	makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(&context),
		make_shared<clang::EmitLLVMOnlyAction>(&context));

	MonoPair<shared_ptr<llvm::Module>> modules =
	compileToModules("", inputOpts, acts);
	shared_ptr<llvm::Module> program = modules.first;

	llvm::legacy::PassManager PM;
	PM.add(new ExplicitAssignPass());
	PM.add(llvm::createPromoteMemoryToRegisterPass());
	PM.add(new AddVariableNamePass());
	PM.add(llvm::createStripSymbolsPass(true));
	PM.add(new PromoteAssertSlicedPass());
	// PM.add(new StripExplicitAssignPass());
	PM.run(*program);

	writeModuleToFile("test.llvm", *program);
}
