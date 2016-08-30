/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include "Compile.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Cloning.h"


#include "util/FileOperations.h"
#include "util/misc.h"
#include "slicingMethods/BruteForce.h"
#include "slicingMethods/CGS.h"
#include "slicingMethods/SyntacticSlicing.h"
#include "slicingMethods/IdSlice.h"
#include "slicingMethods/impact_analysis_for_assignments/ImpactAnalysisForAssignments.h"
#include "core/SliceCandidateValidation.h"

#include "preprocessing/MarkAnalysisPass.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "util/logging.h"

#include "version.h"

using namespace std;
using namespace llvm;

void store(string fileName, Module& module);
void parseArgs(int argc, const char **argv);
CriterionPtr configureCriterion(ModulePtr module);
SlicingMethodPtr configureSlicingMethod(ModulePtr module);
void configureSolver();
void performRemoveFunctions(ModulePtr module, CriterionPtr criterion);
void performInlining(ModulePtr module, CriterionPtr criterion);
void performMarkAnalysis(ModulePtr program);

Function* getSlicedFunction(ModulePtr module, CriterionPtr criterion);


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

enum class SolverOptions{eld, z3, eld_client};
static cl::opt<SolverOptions> SolverMode(cl::desc("Chose smt solver: (Make sure the choosen solver can be found in command line, i.e. set $PATH)"),
	cl::values(
		clEnumValN(SolverOptions::eld, "eld", "Eldarica using command 'eld'"),
		clEnumValN(SolverOptions::eld_client, "eld-client", "Eldarica using command 'eld-client'"),
		clEnumValN(SolverOptions::z3, "z3", "Z3 using command 'z3', requires eld-client as well!"),
		clEnumValEnd),
	cl::init(SolverOptions::eld_client),
	llvm::cl::cat(SlicingCategory)
	);

static llvm::cl::list<string> Includes("I", llvm::cl::desc("Include path"),
	llvm::cl::cat(ClangCategory));

static llvm::cl::opt<string> ResourceDir(
	"resource-dir",
	llvm::cl::desc("Directory containing the clang resource files, "
		"e.g. /usr/local/lib/clang/3.8.0"),
	llvm::cl::cat(ClangCategory));

static llvm::cl::opt<bool> RemoveFunctions("remove-functions", llvm::cl::desc("Removes body of functions from module before slicing. The sliced function is excluded. See -D Option for excluding further functions."),
	llvm::cl::cat(SlicingCategory));
static llvm::cl::list<string> DontRemoveFunction("D", llvm::cl::desc("Functions, which should not be removed by remove functions"),
	llvm::cl::cat(SlicingCategory));

static llvm::cl::opt<bool> InlineFunctions("inline-functions", llvm::cl::desc("Inlines all functions into the sliced function."),
	llvm::cl::cat(SlicingCategory));

static llvm::cl::opt<bool> Heap("heap", llvm::cl::desc("Activate to handle programs with heap."),
	llvm::cl::cat(SlicingCategory));

static llvm::cl::opt<int> MarkInsertThreshold("mark-threshold", llvm::cl::desc("Magic Number. Marks will be inserted until the reduction in the number of paths falls below this threshold."),
	cl::init(10), // Magic value, 10 seems to be a good default value.
	llvm::cl::cat(SlicingCategory));

void parseArgs(int argc, const char **argv) {
	vector<llvm::cl::OptionCategory*> optionCategorys;
	optionCategorys.push_back(&ClangCategory);
	optionCategorys.push_back(&SlicingCategory);
	llvm::cl::HideUnrelatedOptions(optionCategorys);
	llvm::cl::ParseCommandLineOptions(argc, argv);

	Log(Info) << "Slicing the program " << FileName;
	std::stringstream ss;
	for (int i = 0; i < argc; ++i) {
		ss << argv[i] << " ";
	}
	Log(Info) << "The following command was used for execution: "<< ss.str();
}

int main(int argc, const char **argv) {
	Util::configureLogger();
	TIMED_SCOPE(timerBlk, "main");
	Log(Info) << VERSION;
	parseArgs(argc, argv);
	configureSolver();

	ModulePtr program = getModuleFromSource(FileName, ResourceDir, Includes);

	CriterionPtr criterion = configureCriterion(program);
	performRemoveFunctions(program, criterion);
	performInlining(program, criterion);
	performMarkAnalysis(program);

	writeModuleToFile("program.pre_slicing.llvm", *program);

	SlicingMethodPtr method = configureSlicingMethod(program);


	ModulePtr slice;
	{	
		TIMED_SCOPE(timerBlk, "Slicing");
		slice = method->computeSlice(criterion);		
	}	
	
	if (!slice){
		outs() << "An error occured. Could not produce slice. \n";
	} else {
		writeModuleToFile("program.llvm", *program);
		writeModuleToFile("slice.llvm", *slice);
		outs() << "See program.llvm and slice.llvm for the resulting LLVMIRs \n";
	}

	return 0;
}


CriterionPtr configureCriterion(ModulePtr program) {
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
	return criterion;
}

SlicingMethodPtr configureSlicingMethod(ModulePtr program) {
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
		SliceCandidateValidation::activateInitPredicate();
		method = shared_ptr<SlicingMethod>(new CGS(program));
		break;
		case id:
		method = shared_ptr<SlicingMethod>(new IdSlicing(program));
		break;
	}
	return method;
}

void performRemoveFunctions(ModulePtr program, CriterionPtr criterion) {
	if (RemoveFunctions) {
		set<string> notToBeRemoved;
		for (string functionName: DontRemoveFunction) {
			notToBeRemoved.insert(functionName);
			if (!program->getFunction(functionName)) {
				cout << "WARNING: Did not find function, which should not be deleted (-D): " << functionName << endl;
			}
		}

		Function* slicedFunction = getSlicedFunction(program, criterion);

		for (Function& function: *program) {
			if (!Util::isSpecialFunction(function) 
					&& &function != slicedFunction
					&& notToBeRemoved.find(function.getName()) == notToBeRemoved.end()) {

				function.deleteBody();
			}
		}
	}
}

void performInlining(ModulePtr program, CriterionPtr criterion) {
	if (InlineFunctions) {
		Function* slicedFunction = getSlicedFunction(program, criterion);
		writeModuleToFile("program.pre_inlining.llvm", *program);

		bool runInlining = true;
		while (runInlining) {
			runInlining = false;

			std::vector<llvm::CallInst *> toBeInlined;
			for (auto &bb : *slicedFunction) {
				for (auto &instr : bb) {
					if (auto callInst = llvm::dyn_cast<llvm::CallInst>(&instr)) {
						auto fun = callInst->getCalledFunction();
						if (!fun->isDeclaration()) {
							runInlining = true;
							toBeInlined.push_back(callInst);
						}
					}
				}
			}


			for (llvm::CallInst* instr: toBeInlined) {
				llvm::Function* function = instr->getCalledFunction();
				llvm::InlineFunctionInfo InlineInfo;
				if (!llvm::InlineFunction(instr, InlineInfo)){
					std::cout << "ERROR: Could not inline function " << function->getName().str() << std::endl;
					exit(1);
				} else {
					std::cout << "INFO: inlined " << function->getName().str() << std::endl;
				}
			}		
		}

		// Erase all inlined Functions
		vector<Function*> toBeDeleted;
		for (Function& function: *program) {
			if (!Util::isSpecialFunction(function) 
					&& &function != slicedFunction
					&& !function.isDeclaration()) {
				toBeDeleted.push_back(&function);
			}
		}

		for (Function* function: toBeDeleted) {
			function->eraseFromParent();
		}

		writeModuleToFile("program.post_inlining.llvm", *program);
	}
}


void performMarkAnalysis(ModulePtr program) {
	int threshold = MarkInsertThreshold;

	llvm::legacy::PassManager PM;
	PM.add(llvm::createUnifyFunctionExitNodesPass()); 
	PM.add(llvm::createLoopSimplifyPass());
	PM.add(new MarkAnalysisPass(threshold));
	PM.run(*program);
}

Function* getSlicedFunction(ModulePtr program, CriterionPtr criterion) {
	set<Instruction*> criterionInstructions = criterion->getInstructions(*program);
	assert(criterionInstructions.size() == 1 && "Todo: improve implementation to work with multiple criterions");
	Instruction* instruction = *criterionInstructions.begin();
	return instruction->getParent()->getParent();
}

void configureSolver(){
	if (Heap) {
		SliceCandidateValidation::activateHeap();
	}

	switch (SolverMode){
		case SolverOptions::eld:
			SmtSolver::setSolverEld();
			break;
		case SolverOptions::z3:
			SmtSolver::setSolverZ3();
			break;
		case SolverOptions::eld_client:
			SmtSolver::setSolverEldClient();
			break;
	}
}
