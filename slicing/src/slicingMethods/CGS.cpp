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

#include <iostream>

using namespace std;
using namespace llvm;

CandidateNode& CandidateNode::createSuccessor(
		DRM const& drm) {
	
	successors[&drm] = &cge.getCandidateNode(drm.computeSlice(slice));
	
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
	LinearizedFunction& linFunc = cge.linFunc;
	
	pSlice = CloneModule(&cge.module, valueMap);
	
	// Mark all instruction that get sliced
	for(Instruction const& i : Util::getInstructions(linFunc.func)) {
		if(!slice[linFunc[i]]) {
			SlicingPass::toBeSliced(*dyn_cast<Instruction>(valueMap[&i]));
		}
	}
	
	pm.add(new SlicingPass());
	pm.run(*pSlice);
	
	ValidationResult validationResult = SliceCandidateValidation::validate(
		const_cast<Module*>(&cge.module),
		&*pSlice,
		cge.pCriterion,
		&cex);
	
	// Copy the validation state to the internal extended state
	switch(validationResult) {
		case ValidationResult::valid:   state = State::valid;   break;
		case ValidationResult::invalid: state = State::invalid; break;
		case ValidationResult::unknown: state = State::unknown; break;
	}
	
	return *this;
}

CandidateGenerationEngine::CandidateGenerationEngine(
		llvm::Module&       module,
		CriterionPtr const  pCriterion,
		LinearizedFunction& linFunc) :
	module           (module),
	pCriterion       (pCriterion),
	linFunc          (linFunc),
	_instCount       (linFunc.getInstructionCount()),
	_critInstructions(_instCount, 0),
	_pFullSlice      (nullptr),
	_pUnionSlice     (nullptr),
	_pBestValidSlice (nullptr) {
	
	APInt fullSlice(_instCount, 0);
	
	// Mark all instructions that must be in the slice by default
	for(Instruction* i : pCriterion->getInstructions(*const_cast<Function*>(&linFunc.func)->getParent())) {
		_critInstructions.setBit(linFunc[*i]);
	}
	
	fullSlice.setAllBits();
	_pBestValidSlice = _pFullSlice = &getCandidateNode(fullSlice);
}

CandidateNode& CandidateGenerationEngine::generateCandidate(void) {
	
	if(!_pUnionSlice) {
		
		CEXType cex(_instCount);
		
		// Initialize the first counterexample with a 0-vector
		for(unsigned int i = 0; i < _instCount; i++) {
			cex[i] = 0;
		}
		
		return generateCandidate(cex);
		
	} else {
		
		assert(false);
	}
}

CandidateNode& CandidateGenerationEngine::generateCandidate(
		CEXType& cex) {
	
	auto        drmCreation = _drms.emplace(linFunc, cex);
	APInt const dynSlice = drmCreation.first->computeSlice(_critInstructions);
	
	if(_pUnionSlice) {
		_pUnionSlice = &getCandidateNode(_pUnionSlice->slice | dynSlice);
	} else {
		_pUnionSlice = &getCandidateNode(dynSlice);
	}
	
	// TODO: Delete outdated candidates
	
	return *_pUnionSlice;
}

CandidateNode& CandidateGenerationEngine::getCandidateNode(
		APInt const& slice) {
	//cout << "getCandidateNode: ";
	//for(unsigned int i = 0; i < slice.getBitWidth(); i++) {
	//	cout << (slice[i] ? "X" : "_");
	//}
	//cout << " " << _sliceCandidates.size() << " -> ";
	if(_sliceCandidates.find(slice) == _sliceCandidates.end()) {
		_sliceCandidates[slice] = new CandidateNode(*this, slice);
	}
	//cout << _sliceCandidates.size() << " (" << _sliceCandidates[slice] << ")" << endl;
	return *_sliceCandidates[slice];
}

bool CandidateGenerationEngine::updateBestValidSlice(
		CandidateNode& slice) {
	
	if(&slice == _pBestValidSlice && _pBestValidSlice == _pFullSlice) {
		
		// The program can't be sliced at all
		return true;
		
	} else {
		
		assert(slice.size < _pBestValidSlice->size);
	
		_pBestValidSlice = &slice;
		
		// TODO: Delete outdated candidates
		
		return &slice == _pBestValidSlice;
	}
}

ModulePtr CGS::computeSlice(
		CriterionPtr criterion) {
	
	Module&           module             = *getProgram();
	set<Instruction*> critInstructionSet = criterion->getInstructions(module);
	Function&         func               =
		*(*critInstructionSet.begin())->getParent()->getParent();
	
	LinearizedFunction linFunc         (func);
	CEXType            cex             (func.getArgumentList().size());
	
	linFunc.print(_out);
	
	CandidateGenerationEngine cge(module, criterion, linFunc);
	CandidateNode*            pCurCandidate(&cge.generateCandidate());
	
	while(pCurCandidate->validate(cex).getState() !=
		CandidateNode::State::valid) {
		
		printSlice(pCurCandidate->slice) << "  ";
		
		switch(pCurCandidate->getState()) {
			case CandidateNode::State::valid: _out << "valid\n"; break;
			case CandidateNode::State::invalid:
				_out << "invalid ";
				printCounterexample(cex) << "\n";
				break;
			case CandidateNode::State::unknown: _out << "unknown\n"; break;
			case CandidateNode::State::notchecked: assert(false); break;
		}
		
		pCurCandidate =
			pCurCandidate->getState() == CandidateNode::State::invalid ?
			&cge.generateCandidate(cex) :
			&cge.generateCandidate();
	}
	
	cge.updateBestValidSlice(*pCurCandidate);
	
	_out << "Final Slice: ";
	printSlice(pCurCandidate->slice) << "\n";
	
	/*
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
	*/
	return pCurCandidate->getSlicedProgram();
}

raw_ostream& CGS::printCounterexample(
		CEXType const& cex) {
	
	_out << "[";
	
	if(!cex.empty()) {
		_out << " " << cex[0] << " ";
		for(unsigned int i = 1; i < cex.size(); i++) {
			_out << ", " << cex[i] << " ";
		}
	}
	
	_out << "]";
	
	return _out;
}

raw_ostream& CGS::printSlice(
		APInt const& slice) {
	
	for(unsigned int i = 0; i < slice.getBitWidth(); i++) {
		_out << (slice[i] ? "X" : "_");
	}
	
	return _out;
}
