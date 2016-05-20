#include "catch.hpp"

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


void printIR(llvm::Module& module) {
	//for(llvm::Function& function:module) {
		//cout << function.getName().str() << endl;
	//	printIR(function);
	//}

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPrintModulePass(llvm::outs()));
	PM.run(module);
}

TEST_CASE("Slicing pass does remove a statement", "[SlicingPass]") {
	string fileName = "../testdata/simplesyntactic.c";
	std::vector<std::string> includes;
	InputOpts inputOpts(includes, "", fileName, fileName);

	MonoPair<shared_ptr<CodeGenAction>> acts =
	makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
		make_shared<clang::EmitLLVMOnlyAction>());
	MonoPair<shared_ptr<llvm::Module>> modules =
		compileToModules("", inputOpts, acts);

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
    REQUIRE( 0 == 0 );
}
