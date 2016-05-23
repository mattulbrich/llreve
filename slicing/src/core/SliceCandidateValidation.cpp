#include "SliceCandidateValidation.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include "Opts.h"
#include "Preprocess.h"
#include "ModuleSMTGeneration.h"
#include "Serialize.h"

using namespace llvm;
using namespace std;

using smt::SharedSMTRef;


ValidationResult SliceCandidateValidation::validate(llvm::Module* program, llvm::Module* candidate, CounterExample* counterExample){
	PreprocessOpts preprocessOpts(false, false, true);
	MonoPair<string> fileNames("","");
	FileOptions fileOpts = getFileOptions(fileNames);
	SerializeOpts serializeOpts("out.smt", false);

	shared_ptr<Module> programCopy(CloneModule(program));
	shared_ptr<Module> candiateCopy(CloneModule(candidate));

	MonoPair<shared_ptr<Module>> modules(programCopy, candiateCopy);

	auto preprocessedFuns = preprocessFunctions(modules, preprocessOpts);

	vector<SharedSMTRef> smtExprs =
		generateSMT(modules, preprocessedFuns, fileOpts);

	serializeSMT(smtExprs, SMTGenerationOpts::getInstance().MuZ, serializeOpts);

	return unknown;
}
