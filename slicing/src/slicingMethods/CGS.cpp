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

CandidateNode& CandidateNode::createSuccessor(
		DRM const& drm) {
	
	successors[&drm] = &cgs.getCandidateNode(drm.computeSlice(slice));
	
	return *successors[&drm];
}

ModulePtr CandidateNode::getSlicedProgram(void) {
	
	return pSlice;
}

CandidateNode::State CandidateNode::getState(void) {
	
	return state;
}

CandidateNode& CandidateNode::validate(
		CEXType& cex) {
	
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
		const_cast<Module*>(&cgs.module),
		&*pSlice,
		cgs.getCurCriterion(),
		&cex);
	
	// Copy the validation state to the internal extended state
	switch(validationResult) {
		case ValidationResult::valid:   state = State::valid;   break;
		case ValidationResult::invalid: state = State::invalid; break;
		case ValidationResult::unknown: state = State::unknown; break;
	}
	
	return *this;
}

ModulePtr CGS::computeSlice(
		CriterionPtr criterion) {
	
	Module&           module             = *getProgram();
	set<Instruction*> critInstructionSet = criterion->getInstructions(module);
	Function&         func               =
		*(*critInstructionSet.begin())->getParent()->getParent();
	
	LinearizedFunction linFunc         (func);
	APInt              critInstructions(linFunc.getInstructionCount(), 0);
	APInt              unionSlice      (linFunc.getInstructionCount(), 0);
	CandidateNode*     pCurCandidate   (&getCandidateNode(unionSlice));
	bool               performSDS;
	DRM const*         pCurDRM;
	CEXType            cex;
	
	pCurLinFunc   = &linFunc;
	pCurCriterion = criterion;
	
	// Mark all instructions that must be in the slice by default
	for(Instruction* i : criterion->getInstructions(module)) {
		critInstructions.setBit(linFunc[*i]);
	}
	
	while(pCurCandidate->validate(cex).getState() !=
		CandidateNode::State::valid) {
		
		performSDS = true;
		pCurDRM    = nullptr;
		
		// Check whether a counterexample is available
		if(pCurCandidate->getState() == CandidateNode::State::invalid) {
			
			auto cexCreation = _counterexamples.emplace(cex);
			auto drmCreation = _drms.emplace(linFunc, *cexCreation.first);
			
			pCurDRM = &*drmCreation.first;
			
			// Check whether the counterexample and DRM are new
			if(cexCreation.second && drmCreation.second) {
				// Create the union slice
				unionSlice    |= pCurDRM->computeSlice(critInstructions);
				pCurCandidate  = &getCandidateNode(unionSlice);
				performSDS     = false;
			}
		}
		
		if(performSDS) {
			
			// If a counterexample is available, try extending the candidate
			// with the corresponding DRM
			if(pCurDRM) {
				
				pCurCandidate = &pCurCandidate->createSuccessor(*pCurDRM);
				
			} else {
				
				
			}
			
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
