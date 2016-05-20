#include "catch.hpp"

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/SlicingPass.h"
#include "core/AddVariableNamePass.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/IPO.h"



using std::make_shared;
using std::cout;
using std::endl;
using std::shared_ptr;
using std::string;
using clang::CodeGenAction;


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
	    //passManager.add(llvm::createCFGSimplificationPass());
		passManager.run(function);
	}

	string ir;
	llvm::raw_string_ostream stream(ir);

	int i = 0;
	for(llvm::Function& function: *module) {
		for(llvm::BasicBlock& block: function) {
			for(llvm::Instruction& instruction: block) {			
				i++;
				//stream << i << ": " << instruction << "\n";
				if (i == 25) 
				{
					SlicingPass::toBeSliced(instruction);
				}
			}			
		}
	}

	llvm::legacy::PassManager PM;
	PM.add(new AddVariableNamePass());
	PM.add(llvm::createStripSymbolsPass(true));	
	PM.add(new SlicingPass());
	PM.add(llvm::createPrintModulePass(stream));

	PM.run(*module);

	INFO( "=== Resulting IR: ===  \n" << stream.str());

	string errors;
	llvm::raw_string_ostream error_stream(errors);
	bool hasError = llvm::verifyModule(*module, &error_stream);

	INFO( "=== Following Errors were reported: === \n" << error_stream.str());
	CHECK_FALSE( hasError );
	CHECK(false);
}
