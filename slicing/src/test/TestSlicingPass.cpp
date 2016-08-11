/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "catch.hpp"

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "core/SlicingPass.h"
#include "preprocessing/AddVariableNamePass.h"
#include "util/LambdaFunctionPass.h"

#include "llvm/IR/Verifier.h"
#include "llvm/Transforms/IPO.h"



using std::make_shared;
using std::cout;
using std::endl;
using std::shared_ptr;
using std::string;
using clang::CodeGenAction;

using namespace llvm;


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

	string ir;
	llvm::raw_string_ostream stream(ir);

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPromoteMemoryToRegisterPass());
	PM.add(new AddVariableNamePass());
	PM.add(llvm::createStripSymbolsPass(true));
	PM.add(new LambdaFunctionPass([&](Function& function)->bool{
		int i = 0;
		for(llvm::BasicBlock& block: function) {
			for(llvm::Instruction& instruction: block) {
				i++;
				if (i == 13)
				{
					SlicingPass::toBeSliced(instruction);
				}
				stream << i << ": " << instruction << "\n";
			}
		}
		return true;
	}));
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
