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

#include "core/SliceCandidate.h"
#include "util/FileOperations.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "preprocessing/StripExplicitAssignPass.h"

#include "Opts.h"
#include "Preprocess.h"
#include "ModuleSMTGeneration.h"
#include "Serialize.h"

using namespace llvm;
using namespace std;

using smt::SharedSMTRef;

bool SliceCandidateValidation::heap = false;

void SliceCandidateValidation::activateHeap(){
	heap = true;
}

ValidationResult SliceCandidateValidation::validate(SliceCandidate* candidate, CEXType* pCEX){
	assert(candidate != nullptr && "Internal Error: Invalid Arguments.");

	string outputFileName("candidate.smt2");

	auto criterionInstructions = candidate->getCriterion()->getInstructions(*candidate->getProgram());
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
		!heap, // InitPredicate
		map<int, smt::SharedSMTRef>());

	MonoPair<string> fileNames("","");
	FileOptions fileOpts = getFileOptions(fileNames);
	if (!candidate->getCriterion()->isReturnValue()) {
		fileOpts.OutRelation = make_shared<smt::Primitive<string>>("true");
	}

	PreprocessOpts preprocessOpts(false, //showCFG
		false, //showMarkedCFG
		true //Infer Marks
		);

	auto candidateCopy = candidate->copy();
	candidateCopy->computeMarks();
	llvm::legacy::PassManager PM;
	PM.add(new StripExplicitAssignPass());
	PM.run(*candidateCopy->getProgram());
	PM.run(*candidateCopy->getCandidate());
	//candidateCopy->computeMarks();

	MonoPair<shared_ptr<Module>> modules(candidateCopy->getProgram(), candidateCopy->getCandidate());
	auto preprocessedFuns = preprocessCandidate(candidateCopy, preprocessOpts);

	vector<SharedSMTRef> smtExprs =
	generateSMT(modules, preprocessedFuns, fileOpts);

	SerializeOpts serializeOpts(outputFileName, false, false, false, true);
	serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);

	SatResult satResult = SmtSolver::getInstance().checkSat(outputFileName, pCEX);
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

vector<MonoPair<PreprocessedFunction>>
SliceCandidateValidation::preprocessCandidate(SliceCandidatePtr candidate,
		PreprocessOpts opts) {
	vector<MonoPair<PreprocessedFunction>> processedFuns;
	auto funs = zipFunctions(*candidate->getProgram(), *candidate->getCandidate());
	for (auto funPair : funs.get()) {
		preprocessFunction(*funPair.first, "1", opts);
		preprocessFunction(*funPair.second, "2", opts);
	}

	for (auto funPair : funs.get()) {
		BidirBlockMarkMap* markedBlocks1 = candidate->getMarkedBlocksProgram();
		assert(markedBlocks1 != nullptr);
		AnalysisResults results1 = AnalysisResults(*markedBlocks1, findPaths(*markedBlocks1));

		BidirBlockMarkMap* markedBlocks2 = candidate->getMarkedBlocksCandidate();
		AnalysisResults results2 = AnalysisResults(*markedBlocks2, findPaths(*markedBlocks2));

		processedFuns.push_back(
			makeMonoPair(PreprocessedFunction(funPair.first, results1),
			PreprocessedFunction(funPair.second, results2)));
	}
	return processedFuns;
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
		!heap, // InitPredicate
		map<int, smt::SharedSMTRef>());

	MonoPair<string> fileNames("","");
	FileOptions fileOpts = getFileOptions(fileNames);
	if (!criterion->isReturnValue()) {
		fileOpts.OutRelation = make_shared<smt::Primitive<string>>("true");
	}

	PreprocessOpts preprocessOpts(false,
		false,
		true //Infer Marks
		);

	shared_ptr<Module> programCopy(CloneModule(program));
	shared_ptr<Module> candiateCopy(CloneModule(candidate));

	llvm::legacy::PassManager PM;
	PM.add(new StripExplicitAssignPass());
	PM.run(*programCopy);
	PM.run(*candiateCopy);


	MonoPair<shared_ptr<Module>> modules(programCopy, candiateCopy);
	auto preprocessedFuns = preprocessFunctions(modules, preprocessOpts);

	vector<SharedSMTRef> smtExprs =
	generateSMT(modules, preprocessedFuns, fileOpts);

	SerializeOpts serializeOpts(outputFileName, false, false, false, true);
	serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);

	SatResult satResult = SmtSolver::getInstance().checkSat(outputFileName, pCEX);
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


