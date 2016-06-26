#include "SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"
#include "preprocessing/StripExplicitAssignPass.h"

#include "Opts.h"
#include "Preprocess.h"
#include "ModuleSMTGeneration.h"
#include "Serialize.h"

#include "smtSolver/SmtSolver.h"

using namespace llvm;
using namespace std;

using smt::SharedSMTRef;


ValidationResult SliceCandidateValidation::validate(llvm::Module* program, llvm::Module* candidate,
	CriterionPtr criterion, CounterExample* counterExample){
	string outputFileName("candidate.smt");

	SMTGenerationOpts &smtOpts = SMTGenerationOpts::getInstance();
	smtOpts.PerfectSync = true;

	auto criterionInstructions = criterion->getInstructions(*program);
	assert(criterionInstructions.size() > 0 && "Internal Error: Got criterion with no instructions.");
	Function* slicedFunction = nullptr;
	for (Instruction* instruction: criterionInstructions){
		Function* function = instruction->getFunction();
		assert((!slicedFunction || function == slicedFunction) && "Not Supported: Got criterion with multiple functions.");

		slicedFunction = function;
		smtOpts.MainFunction = smtOpts.MainFunction = slicedFunction->getName().str();
	}

	MonoPair<string> fileNames("","");
	FileOptions fileOpts = getFileOptions(fileNames);
	if (!criterion->isReturnValue()) {
		fileOpts.OutRelation = make_shared<smt::Primitive<string>>("true");
	}

	PreprocessOpts preprocessOpts(false, false, true);

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

	SerializeOpts serializeOpts(outputFileName, false, false, false);
	serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);

	SatResult satResult = SmtSolver::getInstance().checkSat(outputFileName);
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
