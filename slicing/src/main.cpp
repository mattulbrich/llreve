#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"


#include "util/FileOperations.h"
#include "slicingMethods/BruteForce.h"
#include "slicingMethods/CGS.h"
#include "slicingMethods/SyntacticSlicing.h"
#include "slicingMethods/impact_analysis_for_assignments/ImpactAnalysisForAssignments.h"
#include "core/SliceCandidateValidation.h"


using namespace std;
using namespace llvm;

void store(string fileName, Module& module);
void parseArgs(int argc, const char **argv);


static llvm::cl::OptionCategory ClangCategory("Clang options",
	"Options for controlling clang.");

static llvm::cl::OptionCategory SlicingCategory("Slicing options",
	"Options for controlling slicing.");

static llvm::cl::opt<std::string> FileName(llvm::cl::Positional,
	llvm::cl::desc("<input file>"),
	llvm::cl::Required);

enum SlicingMethodOptions{syntactic, bruteforce, iaa, cgs};
static cl::opt<SlicingMethodOptions> SlicingMethodOption(cl::desc("Choose slicing method:"),
	cl::values(
		clEnumVal(syntactic , "Classical syntactic slicing, folowd by verification of the slice."),
		clEnumVal(bruteforce, "Bruteforce all slicecandidates, returns smalest."),
		clEnumVal(iaa, "Use impact analysis for assignments to find unneccesary statments."),
		clEnumVal(cgs, "Use counterexample guided slicing to find unneccesary instructions."),
		clEnumValEnd),
	llvm::cl::cat(SlicingCategory),
	llvm::cl::Required);

bool criterionPresent = false;
static llvm::cl::opt<bool,true> CriterionPresentFlag("criterion-present", llvm::cl::desc("Use if the code contains a __criterion function to mark the criterion."), cl::location(criterionPresent),
	llvm::cl::cat(SlicingCategory));
static llvm::cl::alias     CriterionPresentShort("p", cl::desc("Alias for -criterion-present"),
    cl::aliasopt(CriterionPresentFlag), llvm::cl::cat(SlicingCategory));

static llvm::cl::list<string> Includes("I", llvm::cl::desc("Include path"),
	llvm::cl::cat(ClangCategory));

static llvm::cl::opt<string> ResourceDir(
	"resource-dir",
	llvm::cl::desc("Directory containing the clang resource files, "
		"e.g. /usr/local/lib/clang/3.8.0"),
	llvm::cl::cat(ClangCategory));


void parseArgs(int argc, const char **argv) {
	vector<llvm::cl::OptionCategory*> optionCategorys;
	optionCategorys.push_back(&ClangCategory);
	optionCategorys.push_back(&SlicingCategory);
	llvm::cl::HideUnrelatedOptions(optionCategorys);
	llvm::cl::ParseCommandLineOptions(argc, argv);
}

int main(int argc, const char **argv) {
	parseArgs(argc, argv);
	ModulePtr program = getModuleFromSource(FileName, ResourceDir, Includes);

	CriterionPtr criterion;
	CriterionPtr presentCriterion = shared_ptr<Criterion>(new PresentCriterion());
	if (CriterionPresentFlag) {
		if (presentCriterion->getInstructions(*program).size() == 0){
			outs() << "ERROR: Criterion present flag set, but no criterion found! \n";
			exit(1);
		}
		criterion = presentCriterion;
	} else {
		if (presentCriterion->getInstructions(*program).size() > 0){
			outs() << "WARNING: Criterion present flag not set, but criterion found! Slice is for return value!\n";
		}
		criterion = shared_ptr<Criterion>(new ReturnValueCriterion());
	}


	SlicingMethodPtr method;
	switch (SlicingMethodOption) {
		case syntactic:
		method = shared_ptr<SlicingMethod>(new SyntacticSlicing(program));
		break;
		case bruteforce:
		method = shared_ptr<SlicingMethod>(new BruteForce(program));
		break;
		case iaa:
		method = shared_ptr<SlicingMethod>(new ImpactAnalysisForAssignments(program));
		break;
		case cgs:
		method = shared_ptr<SlicingMethod>(new CGS(program));
		break;
	}

	ModulePtr slice = method->computeSlice(criterion);

	if (!slice){
		outs() << "An error occured. Could not produce slice. \n";
	} else {
		writeModuleToFile("program.llvm", *program);
		writeModuleToFile("slice.llvm", *slice);
		outs() << "See program.llvm and slice.llvm for the resulting LLVMIRs \n";
	}

	return 0;
}
