#include "catch.hpp"

#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/SlicingPass.h"
#include "core/AddVariableNamePass.h"
#include "util/LambdaFunctionPass.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/IPO.h"

#include "core/SliceCandidateValidation.h"


using namespace llvm;
using namespace std;

using clang::CodeGenAction;

TEST_CASE("It is possible to call Slice candidate validation", "[SliceCandidateValidation]") {
	string fileName = "../testdata/simple.c";
	std::vector<std::string> includes;
	InputOpts inputOpts(includes, "", fileName, fileName);

	MonoPair<shared_ptr<CodeGenAction>> acts =
	makeMonoPair(make_shared<clang::EmitLLVMOnlyAction>(),
		make_shared<clang::EmitLLVMOnlyAction>());
	MonoPair<shared_ptr<llvm::Module>> modules =
		compileToModules("", inputOpts, acts);

	shared_ptr<llvm::Module> program = modules.first;

	{
		llvm::legacy::PassManager PM;
		PM.add(llvm::createPromoteMemoryToRegisterPass());		
		PM.add(new AddVariableNamePass());
		PM.add(llvm::createStripSymbolsPass(true));
		PM.run(*program);
	}

	auto sliceCandidate = CloneModule(&*program);

	{
		string ir;
		llvm::raw_string_ostream stream(ir);

		llvm::legacy::PassManager PM;
		PM.add(new LambdaFunctionPass([&](Function& function)->bool{
			int i = 0;
			for(llvm::BasicBlock& block: function) {
				for(llvm::Instruction& instruction: block) {			
					i++;				
					if (i == 1) 
					{
						SlicingPass::toBeSliced(instruction);
					}
					stream << i << ": " << instruction << "\n";
				}			
			}
			return true;
		}));
		PM.add(new SlicingPass());
		PM.run(*sliceCandidate);

		WARN(stream.str());
	}

	SliceCandidateValidation::validate(&*program, &*sliceCandidate);



}