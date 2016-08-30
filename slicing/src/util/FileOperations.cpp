/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "FileOperations.h"

#include "preprocessing/AddVariableNamePass.h"
#include "preprocessing/PromoteAssertSlicedPass.h"
#include "preprocessing/ExplicitAssignPass.h"
#include "preprocessing/FixNamesPass.h"
#include "preprocessing/ReplaceUndefPass.h"
 
#include "core/Util.h"

#include "Opts.h"
#include "Compile.h"
#include "Helper.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/Transforms/Utils/Cloning.h"


#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Verifier.h"

#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/Constants.h"

#include "util/LambdaFunctionPass.h"

#include "util/logging.h"

using namespace std;
using namespace llvm;
using namespace clang;

shared_ptr<llvm::Module> getModuleFromSource(string fileName, string resourceDir, vector<std::string> includes){
	TIMED_SCOPE(timerBlk, "LoadModuleFromSource");
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

	writeModuleToFile("program.original.llvm", *program);

	llvm::legacy::PassManager PM;
	PM.add(new ExplicitAssignPass());
	PM.add(llvm::createPromoteMemoryToRegisterPass());
	PM.add(new LambdaModulePass([](llvm::Module& module)->bool{
			writeModuleToFile("program.post_promote_mem2reg.llvm", module);
			return false;
		}));
	PM.add(new AddVariableNamePass());
	PM.add(llvm::createStripSymbolsPass(true));
	PM.add(new PromoteAssertSlicedPass());
	PM.add(new FixNamesPass());
	PM.add(new ReplaceUndefPass());

	PM.run(*program);

	bool hasError = llvm::verifyModule(*program, &errs());
	assert(!hasError && "Error during initial construction of module!");

	for (Function& function: *program) {
		for (Instruction& instruction : Util::getInstructions(function)) {
			for (Use& use:instruction.operands()) {
				if (isa<UndefValue>(use)){
					writeModuleToFile("program.llvm", *program);
					// Todo this is actually an input error and should be handled
					// by exception.
					logError("Found undefined Variable, make sure you define all Variables.");
					abort();
				}
			}
		}
	}

	writeModuleToFile("program.post_preprocessing.llvm", *program);
	return program;
}

void writeModuleToFile(string fileName, llvm::Module& module) {
	std::error_code EC;
	raw_fd_ostream programOut(StringRef(fileName), EC, llvm::sys::fs::OpenFlags::F_None);

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPrintModulePass(programOut));
	PM.run(module);
}
