#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"


#include "util/FileOperations.h"
#include "slicingMethods/BruteForce.h"
#include "slicingMethods/SyntacticSlicing.h"


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

enum SlicingMethodOptions{syntactic, bruteforce};
static cl::opt<SlicingMethodOptions> SlicingMethodOption(cl::desc("Choose slicing method:"),
	cl::values(
		clEnumVal(syntactic , "Classical syntactic slicing, folowd by verification of the slice."),
		clEnumVal(bruteforce, "Bruteforce all slicecandidates, returns smalest."),
		clEnumValEnd),
	llvm::cl::cat(SlicingCategory),
	llvm::cl::Required);

static llvm::cl::opt<bool> CriterionPresent("criterion-present", llvm::cl::desc("Use if the code contains a __criterion function to mark the criterion."),
	llvm::cl::cat(SlicingCategory));
static llvm::cl::alias     CriterionPresentShort("p", cl::desc("Alias for -criterion-present"),
	cl::aliasopt(CriterionPresent), llvm::cl::cat(SlicingCategory));

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

void store(string fileName, Module& module) {
	std::error_code EC;
	raw_fd_ostream programOut(StringRef(fileName), EC, llvm::sys::fs::OpenFlags::F_None);

	llvm::legacy::PassManager PM;
	PM.add(llvm::createPrintModulePass(programOut));
	PM.run(module);
}

int main(int argc, const char **argv) {
	parseArgs(argc, argv);
	ModulePtr program = getModuleFromFile(FileName, ResourceDir, Includes);

	SMTGenerationOpts &smtOpts = SMTGenerationOpts::getInstance();
	smtOpts.PerfectSync = true;

	if (CriterionPresent) {
		smtOpts.DisableOutInv = true;
	}

	for (Function& function:*program) {
		if (function.getName() != "__criterion"
			&& function.getName() != "__mark") {
			smtOpts.MainFunction = function.getName().str();
			break;
		}
	}


	SlicingMethodPtr method;
	switch (SlicingMethodOption) {
		case syntactic:
		method = shared_ptr<SlicingMethod>(new SyntacticSlicing(program));
		break;
		case bruteforce:
		method = shared_ptr<SlicingMethod>(new BruteForce(program));
		break;
	}

	ModulePtr slice = method->computeSlice(Criterion());

	if (!slice){
		outs() << "An error occured. Could not produce slice. \n";
	} else {
		store("program.llvm", *program);
		store("slice.llvm", *slice);
		outs() << "See program.llvm and slice.llvm for the resulting LLVMIRs \n";
	}

	return 0;
}
