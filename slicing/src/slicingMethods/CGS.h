#pragma once

#include "core/Criterion.h"
#include "SlicingMethod.h"

#include "dynamic/DRM.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include <list>
#include <set>
#include <vector>

class CandidateGenerationEngine;
class CGS;

class CandidateNode {
	
	public:
	
	enum class State {valid, invalid, unknown, notchecked};
	
	CandidateGenerationEngine& cge;
	llvm::APInt  const         slice;
	unsigned int const         size;
	
	CandidateNode(CandidateGenerationEngine& cge, llvm::APInt const& slice) :
		cge   (cge),
		slice (slice),
		size  (slice.countPopulation()),
		state (State::notchecked),
		pSlice(nullptr) {}
	
	CandidateNode& validate        (CEXType& cex);
	State          getState        (void);
	ModulePtr      getSlicedProgram(void);
	
	CandidateNode& createSuccessor(DRM const& drm);
	
	private:
	
	State     state;
	ModulePtr pSlice;
	
	std::map<DRM const*, CandidateNode*> successors;
	std::set<            CandidateNode*> predecessors;
};

class CandidateGenerationEngine {
	
	public:
	
	llvm::Module&       module;
	CriterionPtr const  pCriterion;
	LinearizedFunction& linFunc;
	
	CandidateGenerationEngine(
		llvm::Module&       module,
		CriterionPtr const  pCriterion,
		LinearizedFunction& linFunc);
	
	CandidateNode& generateCandidate(void);
	CandidateNode& generateCandidate(CEXType& cex);
	CandidateNode& getCandidateNode (llvm::APInt const& slice);
	
	// Returns true if the new slice is the union slice and thus minimal
	bool updateBestValidSlice(CandidateNode& slice);
	
	private:
	
	unsigned int const _instCount;
	llvm::APInt        _critInstructions;
	CandidateNode*     _pFullSlice;
	CandidateNode*     _pUnionSlice;
	CandidateNode*     _pBestValidSlice;
	
	std::set<DRM const,                         DRMCompare>   _drms;
	std::map<llvm::APInt const, CandidateNode*, APIntCompare> _sliceCandidates;
};

class CGS : public SlicingMethod {
	
	public:
	
	llvm::Module const& module;
	
	CGS(ModulePtr program, llvm::raw_ostream& ostream = llvm::outs()) :
		SlicingMethod(program), module(*getProgram()), _out(ostream) {}
	
	virtual ModulePtr computeSlice(CriterionPtr c) override;
	
	private:
	
	llvm::raw_ostream& _out;
	
	llvm::raw_ostream& printCounterexample(CEXType const& cex);
	llvm::raw_ostream& printSlice(llvm::APInt const& slice);
};
