/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "SliceCandidateValidation.h"

#include "util/FileOperations.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "preprocessing/StripExplicitAssignPass.h"

#include "Opts.h"
#include "Preprocess.h"
#include "ModuleSMTGeneration.h"
#include "Serialize.h"

#include "util/logging.h"

using namespace llvm;
using namespace std;
using namespace llreve::opts;

using smt::SharedSMTRef;

bool SliceCandidateValidation::heap = false;
bool SliceCandidateValidation::initPredicate = false;

void SliceCandidateValidation::activateHeap(){
	heap = true;
}

void SliceCandidateValidation::activateInitPredicate(){
	initPredicate = true;
}

ValidationResult SliceCandidateValidation::validate(llvm::Module* program, llvm::Module* candidate,
	CriterionPtr criterion, CEXType* pCEX){
	string outputFileName("candidate.smt2");

	auto criterionInstructions = criterion->getInstructions(*program);
	assert(criterionInstructions.size() > 0 && "Internal Error: Got criterion with no instructions.");
	Function* slicedFunction = nullptr;
	for (Instruction* instruction: criterionInstructions){
		Function* function = instruction->getFunction();
		assert((!slicedFunction || function == slicedFunction) && "Not Supported: Got criterion with multiple functions.");

		slicedFunction = function;
	}
	assert((slicedFunction) && "Did not find sliced function.");

	SMTGenerationOpts &smtOpts = SMTGenerationOpts::getInstance();
	// don't assign smtOpts member variables directly but use initialize
	// see https://github.com/mattulbrich/llreve/issues/10 for details
	smtOpts.initialize(
		slicedFunction->getName().str(),
		heap, // Heap
		false, false, false,
		false, // No-Byte-Heap
		false, false, false,
		true, // PerfectSync
		false, false, false, false,
		initPredicate, // InitPredicate
		map<int, smt::SharedSMTRef>());

	MonoPair<string> fileNames("","");
	FileOptions fileOpts = getFileOptions(fileNames);
	if (!criterion->isReturnValue()) {
		fileOpts.OutRelation = make_unique<ConstantBool>(true);
	}

	PreprocessOpts preprocessOpts(false,
		false,
		false //Infer Marks
		);

	shared_ptr<Module> programCopy(CloneModule(program));
	shared_ptr<Module> candiateCopy(CloneModule(candidate));

	llvm::legacy::PassManager PM;
	PM.add(new StripExplicitAssignPass());
	PM.run(*programCopy);
	PM.run(*candiateCopy);
	writeModuleToFile("candidate.llvm", *candiateCopy);
	{
		TIMED_SCOPE(timerBlk, "Reve");
		MonoPair<shared_ptr<Module>> modules(programCopy, candiateCopy);
		auto preprocessedFuns = preprocessFunctions(modules, preprocessOpts);

		vector<SharedSMTRef> smtExprs =
		generateSMT(modules, preprocessedFuns, fileOpts);

		SerializeOpts serializeOpts(outputFileName, false, false, false, true);
		serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);
	}

	SatResult satResult;
	{
		TIMED_SCOPE(timerBlk, "SMTSolver");
		satResult = SmtSolver::getInstance().checkSat(outputFileName, pCEX);
	}
	Log(Info) << "SMT Solver Result: " << satResult;
	ValidationResult result;

	switch (satResult) {
		case SatResult::sat:
		result = ValidationResult::valid;
		break;
		case SatResult::unsat:
		result = ValidationResult::invalid;
		break;
		default:
		result = ValidationResult::unknown;
		break;
	}

	return result;
}


