#include "CGS.h"

#include "core/SlicingPass.h"
#include "core/Util.h"
#include "dynamic/DRM.h"
#include "util/misc.h"

#include "llvm/Transforms/Utils/Cloning.h"

using namespace std;
using namespace llvm;

shared_ptr<Module> CGS::computeSlice(
		CriterionPtr criterion) {
	
	Module& program = *getProgram();
	Function& func = getFirstNonSpecialFunction(program);
	LinearizedFunction linFunc(func);
	
	// TODO: Change for counterexample
	// (All arguments are set to 0)
	int argCount = linFunc.func.getArgumentList().size();
	uint64_t* input = new uint64_t[argCount];
	for(int i = 0; i < argCount; i++) input[i] = 0;
	
	linFunc.print(_ostream);
	
	DRM testDRM(linFunc, input);
	
	testDRM.print(_ostream);
	
	
	ValueToValueMapTy valueMap;
	ModulePtr sliceCandidate = CloneModule(&program, valueMap);
	
	APInt apriori(linFunc.getInstructionCount(), 0);
	for(Instruction* i : criterion->getInstructions(program)) {
		apriori.setBit(linFunc[*i]);
	}
	
	APInt const& slice = testDRM.computeSlice(apriori);
	
	for(Instruction& i : Util::getInstructions(func)) {
		if(!slice[linFunc[i]]) {
			SlicingPass::toBeSliced(*dyn_cast<Instruction>(valueMap[&i]));
		}
	}
	
	llvm::legacy::PassManager pm;
	pm.add(new SlicingPass());
	pm.run(*sliceCandidate);
	
	return sliceCandidate;
}

Function& CGS::getFirstNonSpecialFunction(
		Module& module) {
	
	for(Function& i : module) {
		if(!Util::isSpecialFunction(i)) {
			return i;
		}
	}
}
