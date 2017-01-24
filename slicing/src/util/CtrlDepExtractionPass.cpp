#include "CtrlDepExtractionPass.h"

#include "core/DependencyGraphPasses.h"

#include "llvm/IR/Module.h"

#include <cassert>

using namespace std;
using namespace llvm;

char CtrlDepExtractionPass::ID = 0;

void CtrlDepExtractionPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<CDGPass>();
}

CtrlDepExtractionPass::ResultType CtrlDepExtractionPass::getCtrlDependencies(
		LinearizedFunction const& linFunc) {
	
	ResultType result(linFunc.getInstructionCount());
	
	return getCtrlDependencies(linFunc, result);
}
	
CtrlDepExtractionPass::ResultType& CtrlDepExtractionPass::getCtrlDependencies(
		LinearizedFunction const& linFunc,
		ResultType&               result) {
	
	assert(
		result.size() == linFunc.getInstructionCount() &&
		"Size of result vector must be equal to the number of instructions");
	
	legacy::PassManager pm;
	
	pm.add(new PostDominatorTree());
	pm.add(new CDGPass());
	pm.add(new CtrlDepExtractionPass(linFunc, result));
	
	pm.run(*const_cast<Module*>(linFunc.func.getParent()));
	
	return result;
}
	
bool CtrlDepExtractionPass::runOnFunction(
		Function& func) {
	
	// Check whether this is the correct function
	if(&func != &_linFunc.func) {
		return false;
	}
	
	CDGPass const& cdg = getAnalysis<CDGPass>();
	
	for(Instruction& i : Util::getInstructions(func)) {
		
		unordered_set<Instruction const*>& instDependencies =
			_dependencies[_linFunc[i]];
		
		instDependencies.clear();
		
		// Predecessors that point to no instruction (root node) are not copied
		for(auto& j : cdg[i].predecessors) {
			if(j->innerNode) {
				instDependencies.insert(j->innerNode);
			}
		}
	}
	
	return false;
}
