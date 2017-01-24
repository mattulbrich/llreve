#include "CGS.h"

#include "core/SliceCandidateValidation.h"
#include "core/SlicingPass.h"
#include "core/Util.h"
#include "util/CtrlDepExtractionPass.h"
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
	
	APInt                     fullSlice(_instCount, 0);
	queue<Instruction const*> critInstAccumulator;
	
	CtrlDepExtractionPass::ResultType const ctrlDependencies =
		CtrlDepExtractionPass::getCtrlDependencies(linFunc);
	
	// Fill the accumulator with the criterion instructions itself
	for(Instruction* i : pCriterion->getInstructions(*const_cast<Function*>(&linFunc.func)->getParent())) {
		critInstAccumulator.push(i);
	}
	
	// Add the control dependency closure to the accumulator
	while(!critInstAccumulator.empty()) {
		
		unsigned int const instIndex = linFunc[*critInstAccumulator.front()];
		
		critInstAccumulator.pop();
		
		if(!_critInstructions[instIndex]) {
			_critInstructions.setBit(instIndex);
			for(Instruction const* i : ctrlDependencies[instIndex]) {
				critInstAccumulator.push(i);
			}
		}
	}
	
	fullSlice.setAllBits();
	_pBestValidSlice = _pFullSlice = &getCandidateNode(fullSlice);
}

CandidateNode& CandidateGenerationEngine::generateCandidate(void) {
	
	if(_pUnionSlice) {
		
		unsigned int const minSize        = _pUnionSlice->size + 1;
		CandidateNode*     pBestCandidate = _pFullSlice;
		
		for(DRM const& i : _drms) {
			
			CandidateNode&     candidate = _pUnionSlice->createSuccessor(i);
			unsigned int const newSize   = candidate.size;
			
			if(newSize >= minSize && newSize < pBestCandidate->size) {
				pBestCandidate = &candidate;
			}
		}
		
		return *pBestCandidate;
		
	} else {
		
		CEXType cex(_instCount);
		
		// Initialize the first counterexample with a 0-vector
		for(unsigned int i = 0; i < _instCount; i++) {
			cex[i] = 0;
		}
		
		return generateCandidate(cex);
	}
}

CandidateNode& CandidateGenerationEngine::generateCandidate(
		CEXType& cex) {
	
	auto  drmCreation = _drms.emplace(linFunc, cex);
	APInt dynSlice    = drmCreation.first->computeSlice(_critInstructions);
	
	// If there's no union slice yet, the dynamic slice is the union slice
	if(!_pUnionSlice) {
		return *(_pUnionSlice = &getCandidateNode(dynSlice));
	}
	
	CandidateNode const* const _pOldUnionSlice = _pUnionSlice;
	
	_pUnionSlice = &getCandidateNode(_pUnionSlice->slice | dynSlice);
	
	// Check whether the dynamic slice yielded a new union slice
	return
		_pUnionSlice != _pOldUnionSlice ? *_pUnionSlice : generateCandidate();
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
	
	LinearizedFunction linFunc(func);
	CEXType            cex    (func.getArgumentList().size());
	
	_out << "\n";
	_out << "The following lines show a mapping of integer values to LLVM instructions.\n";
	_out << "The mapping is used for the execution traces to show which instruction\n";
	_out << "has been executed. A slice is displayed in the form X_XX with as many\n";
	_out << "digits as there are instructions in the program. For each removed\n";
	_out << "instruction 'X' is replaced with '_'\n\n";
	linFunc.print(_out);
	_out << "\n";
	
	CandidateGenerationEngine cge(module, criterion, linFunc);
	CandidateNode*            pCurCandidate(&cge.generateCandidate());
	
	// Counterexamples are only necessary if there's at least one function
	// parameter
	if(!cex.empty()) {
		SliceCandidateValidation::activateInitPredicate();
	}
	
	_out << "\n";
	_out << "Current slice candidate: ";
	printSlice(pCurCandidate->slice) << "\n";
	_out << " -> ";
	
	while(pCurCandidate->validate(cex).getState() !=
		CandidateNode::State::valid) {
		
		switch(pCurCandidate->getState()) {
			case CandidateNode::State::valid: _out << "valid\n"; break;
			case CandidateNode::State::invalid:
				_out << "invalid\n";
				_out << " -> new counterexample: ";
				printCounterexample(cex) << "\n";
				break;
			case CandidateNode::State::unknown: _out << "unknown\n"; break;
			case CandidateNode::State::notchecked: assert(false); break;
		}
		
		pCurCandidate =
			pCurCandidate->getState() == CandidateNode::State::invalid ?
			&cge.generateCandidate(cex) :
			&cge.generateCandidate();
		
		_out << "\n";
		_out << "Current slice candidate: ";
		printSlice(pCurCandidate->slice) << "\n";
		_out << " -> ";
	}
	
	cge.updateBestValidSlice(*pCurCandidate);
	
	_out << "[final]\n";
	//_out << "Final Slice: ";
	//printSlice(pCurCandidate->slice) << "\n";
	
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
