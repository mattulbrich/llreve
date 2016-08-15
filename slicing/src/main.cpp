#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"


#include "util/FileOperations.h"
#include "util/misc.h"
#include "slicingMethods/BruteForce.h"
#include "slicingMethods/CGS.h"
#include "slicingMethods/SyntacticSlicing.h"
#include "slicingMethods/IdSlice.h"
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

enum SlicingMethodOptions{syntactic, bf, iaa, cgs, id};
static cl::opt<SlicingMethodOptions> SlicingMethodOption(cl::desc("Choose slicing method:"),
	cl::values(
		clEnumVal(syntactic , "Classical syntactic slicing, folowd by verification of the slice."),
		clEnumVal(bf, "Bruteforce all slicecandidates, returns smalest."),
		clEnumVal(iaa, "Use impact analysis for assignments to find unneccesary statments."),
		clEnumVal(cgs, "Use counterexample guided slicing to find unneccesary instructions."),
		clEnumVal(id, "Use the program it self as slice and verify validity."),
		clEnumValEnd),
	llvm::cl::cat(SlicingCategory),
	llvm::cl::Required);

enum CriterionModes{present, returnValue, automatic};
static cl::opt<CriterionModes> CriterionMode(cl::desc("Chose crietion mode:"),
	cl::values(
		clEnumValN(present, "p","Chose if __criterion is present."),
		clEnumValN(returnValue, "r","Chose to slice after return value."),
		clEnumVal(automatic, "Chose to slice for __criterion if present, return value otherwise. (default)"),
		clEnumValEnd),
	cl::init(automatic),
	llvm::cl::cat(SlicingCategory)
	);

static llvm::cl::list<string> Includes("I", llvm::cl::desc("Include path"),
	llvm::cl::cat(ClangCategory));

static llvm::cl::opt<string> ResourceDir(
	"resource-dir",
	llvm::cl::desc("Directory containing the clang resource files, "
		"e.g. /usr/local/lib/clang/3.8.0"),
	llvm::cl::cat(ClangCategory));

static llvm::cl::opt<bool> RemoveFunctions("remove-functions", llvm::cl::desc("Removes unused functions from module before slicing."),
	llvm::cl::cat(SlicingCategory));

static llvm::cl::opt<bool> Heap("heap", llvm::cl::desc("Activate to handle programs with heap."),
	llvm::cl::cat(SlicingCategory));

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

	switch (CriterionMode) {
		case present:
			if (presentCriterion->getInstructions(*program).size() == 0){
				outs() << "ERROR: Criterion present flag set, but no criterion found! \n";
				exit(1);
			}
			criterion = presentCriterion;
			break;
		case returnValue:
			if (presentCriterion->getInstructions(*program).size() > 0){
				outs() << "WARNING: Criterion present flag not set, but criterion found! Slice is for return value!\n";
			}
			criterion = shared_ptr<Criterion>(new ReturnValueCriterion());
			break;
		default:
			if (presentCriterion->getInstructions(*program).size() == 0){
				criterion = shared_ptr<Criterion>(new ReturnValueCriterion());
			} else {
				criterion = presentCriterion;
			}
		break;
	}

	if (Heap) {
		SliceCandidateValidation::activateHeap();
	}

	SlicingMethodPtr method;
	switch (SlicingMethodOption) {
		case syntactic:
		method = shared_ptr<SlicingMethod>(new SyntacticSlicing(program));
		break;
		case bf:
		method = shared_ptr<SlicingMethod>(new BruteForce(program));
		break;
		case iaa:
		method = shared_ptr<SlicingMethod>(new ImpactAnalysisForAssignments(program));
		break;
		case cgs:
		method = shared_ptr<SlicingMethod>(new CGS(program));
		break;
		case id:
		method = shared_ptr<SlicingMethod>(new IdSlicing(program));
		break;
	}


	if (RemoveFunctions) {
		set<Instruction*> criterionInstructions = criterion->getInstructions(*program);
		assert(criterionInstructions.size() == 1 && "Todo: improve implementation to work with multiple criterions");
		Instruction* instruction = *criterionInstructions.begin();
		Function* fun = instruction->getParent()->getParent();
		vector<Function*> removeFun;
		for (Function& function: *program) {
			if (!Util::isSpecialFunction(function) && &function != fun) {
				removeFun.push_back(&function);
			}
		}
		for (Function* function:removeFun) {
			Function* exFun = Function::Create(function->getFunctionType(), llvm::GlobalValue::LinkageTypes::ExternalLinkage, Twine(function->getName()), &*program);
			function->replaceAllUsesWith(exFun);
			function->eraseFromParent();
		}
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
