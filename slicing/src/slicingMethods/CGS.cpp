#include "CGS.h"

#include "core/SliceCandidateValidation.h"
#include "core/SlicingPass.h"
#include "core/Util.h"
#include "util/misc.h"

#include "llvm/Transforms/Utils/Cloning.h"

#include <algorithm>
#include <array>
#include <cassert>
#include <unordered_set>

using namespace std;
using namespace llvm;

ModulePtr CandidateNode::getSlicedProgram(void) {
	
	return pSlice;
}

CandidateNode::State CandidateNode::getState(void) {
	
	return state;
}

CandidateNode& CandidateNode::validate(
		DRM::CEXType& cex) {
	
	assert(!pSlice);
	
	ValueToValueMapTy   valueMap;
	legacy::PassManager pm;
	LinearizedFunction& linFunc = cgs.getCurLinFunction();
	
	pSlice = CloneModule(&cgs.module, valueMap);
	
	// Mark all instruction that get sliced
	for(Instruction const& i : Util::getInstructions(linFunc.func)) {
		if(!slice[linFunc[i]]) {
			SlicingPass::toBeSliced(*dyn_cast<Instruction>(valueMap[&i]));
		}
	}
	
	pm.add(new SlicingPass());
	pm.run(*pSlice);
	
	ValidationResult validationResult = SliceCandidateValidation::validate(
		const_cast<Module*>(&cgs.module), &*pSlice, cgs.getCurCriterion());
	
	// Copy the validation state to the internal extended state
	switch(validationResult) {
		case ValidationResult::valid:   state = State::valid;   break;
		case ValidationResult::invalid: state = State::invalid; break;
		case ValidationResult::unknown: state = State::unknown; break;
	}
	
	// Extract the counterexample
	if(state == State::invalid) {
		
	}
	
	return *this;
}

ModulePtr CGS::computeSlice(
		CriterionPtr criterion) {
	
	Module&           module             = *getProgram();
	set<Instruction*> critInstructionSet = criterion->getInstructions(module);
	Function&         func               =
		*(*critInstructionSet.begin())->getParent()->getParent();
	//ModulePtr         sliceCandidate;
	//unordered_set<CandidateNode*> 
	
	LinearizedFunction linFunc         (func);
	APInt              critInstructions(linFunc.getInstructionCount(), 0);
	APInt              unionSlice      (linFunc.getInstructionCount(), 0);
	CandidateNode*     pCurCandidate   (&getCandidateNode(unionSlice));
	bool               performSDS;
	
	pCurLinFunc   = &linFunc;
	pCurCriterion = criterion;
	
	// Array to store the current counterexample
	//uint64_t* cex = new uint64_t[linFunc.func.getArgumentList().size()];
	DRM::CEXType cex;
	
	// Mark all instructions that must be in the slice by default
	for(Instruction* i : criterion->getInstructions(module)) {
		critInstructions.setBit(linFunc[*i]);
	}
	
	while(pCurCandidate->validate(cex).getState() !=
		CandidateNode::State::valid) {
		
		performSDS = true;
		
		// Check whether a counterexample is available
		if(pCurCandidate->getState() == CandidateNode::State::invalid) {
			
			auto       cexCreation = _counterexamples.emplace(cex);
			DRM const* pLatestDRM  = nullptr;
			
			// Check whether the counterexample is new
			if(cexCreation.second) {
				
				auto drmCreation = _drms.emplace(linFunc, *cexCreation.first);
				pLatestDRM       = &*drmCreation.first;
				
				// Check whether the resulting DRM is new
				if(drmCreation.second) {
					// Create the union slice
					unionSlice    |= pLatestDRM->computeSlice(critInstructions);
					pCurCandidate  = &getCandidateNode(unionSlice);
					performSDS     = false;
				}
			}
		}
		
		if(performSDS) {
			assert(false);
			// TODO: perform SDS step
		}
	}
	
	return pCurCandidate->getSlicedProgram();
	/*
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
	*/
}

CandidateNode& CGS::getCandidateNode(
		APInt const& slice) {
	
	if(_sliceCandidates.find(slice) == _sliceCandidates.end()) {
		_sliceCandidates[slice] = new CandidateNode(*this, slice);
	}
	
	return *_sliceCandidates[slice];
}

CriterionPtr& CGS::getCurCriterion(void) {
	
	return pCurCriterion;
}
	
LinearizedFunction& CGS::getCurLinFunction(void) {
	
	return *pCurLinFunc;
}
