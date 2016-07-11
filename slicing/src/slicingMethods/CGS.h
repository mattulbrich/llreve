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

class CGS;

class CandidateNode {
	
	public:
	
	enum class State {valid, invalid, unknown, notchecked};
	
	CGS&               cgs;
	llvm::APInt const& slice;
	
	CandidateNode(CGS& cgs, llvm::APInt const& slice) :
		cgs(cgs), slice(slice), state(State::notchecked), pSlice(nullptr) {}
	
	CandidateNode& validate        (CEXType& cex);
	State          getState        (void);
	ModulePtr      getSlicedProgram(void);
	
	private:
	
	State     state;
	ModulePtr pSlice;
	
	std::map<DRM const*, CandidateNode*> successors;
	std::set<            CandidateNode*> predecessors;
};

class CGS : public SlicingMethod {
	
	public:
	
	llvm::Module const& module;
	
	CGS(ModulePtr program, llvm::raw_ostream& ostream = llvm::outs()) :
		SlicingMethod(program), module(*getProgram()), pCurLinFunc(nullptr) {}
	
	virtual ModulePtr computeSlice(CriterionPtr c) override;
	
	LinearizedFunction& getCurLinFunction(void);
	CriterionPtr&       getCurCriterion  (void);
	CandidateNode&      getCandidateNode (llvm::APInt const& slice);
	
	private:
	
	LinearizedFunction* pCurLinFunc;
	CriterionPtr        pCurCriterion;
	
	std::set<CEXType const>                                   _counterexamples;
	std::set<DRM const,                         DRMCompare>   _drms;
	std::map<llvm::APInt const, CandidateNode*, APIntCompare> _sliceCandidates;
};
