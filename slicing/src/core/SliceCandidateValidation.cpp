#include "SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include "Opts.h"
#include "Preprocess.h"
#include "ModuleSMTGeneration.h"
#include "Serialize.h"

#include "smtSolver/SmtSolver.h"

using namespace llvm;
using namespace std;

using smt::SharedSMTRef;


ValidationResult SliceCandidateValidation::validate(llvm::Module* program, llvm::Module* candidate, CounterExample* counterExample){
	string outputFileName("candidate.smt");

	PreprocessOpts preprocessOpts(false, false, true);
	MonoPair<string> fileNames("","");
    FileOptions fileOpts = getFileOptions(fileNames);
    if (CriterionPresent) {
        fileOpts.OutRelation = make_shared<smt::Primitive<string>>("true");
    }
	SerializeOpts serializeOpts(outputFileName, false, false);

	shared_ptr<Module> programCopy(CloneModule(program));
	shared_ptr<Module> candiateCopy(CloneModule(candidate));

	MonoPair<shared_ptr<Module>> modules(programCopy, candiateCopy);

	auto preprocessedFuns = preprocessFunctions(modules, preprocessOpts);

	vector<SharedSMTRef> smtExprs =
		generateSMT(modules, preprocessedFuns, fileOpts);

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
