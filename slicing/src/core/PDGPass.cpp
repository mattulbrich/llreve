#include "PDGPass.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/Support/Casting.h"

#include <iostream>
#include <queue>
#include <stdexcept>

using namespace std;
using namespace llvm;

static RegisterPass<PDGPass> tmp("pdg-creation", "PDG Creation", true, true);

char PDGPass::ID = 0;

BasicBlock* PDGPass::computeCtrlDependency(
		BasicBlock const&        bb,
		PostDominatorTree const& pdt) {
	
	queue<BasicBlock const*>         toCheck;
	unordered_set<BasicBlock const*> markedToCheck;
	
	toCheck.push(&bb);
	
	while(!toCheck.empty()) {
		
		BasicBlock const& curBB = *toCheck.front();
		
		toCheck.pop();
		
		// Check whether 'curBB' is the control dependency we're looking for
		if(!pdt.dominates(&bb, &curBB)) {
			return const_cast<BasicBlock*>(&curBB);
		}
		
		// Prepare the basic block's predecessors for dependency checking in future
		for(BasicBlock const* i : predecessors(&curBB)) {
			if(markedToCheck.find(i) == markedToCheck.end()) {
				toCheck      .push(i);
				markedToCheck.insert(i);
			}
		}
	}
	
	return NULL;
}

void PDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<PostDominatorTree>();
}

Instruction* PDGPass::getCtrlDependency(
		Instruction const& instr) const {
	
	try {
		return _ctrlDependencies.at(instr.getParent());
	} catch(out_of_range&) {
		return NULL;
	}
}

unordered_set<Instruction*>& PDGPass::getDataDependencies(
		Instruction const&           instr,
		unordered_set<Instruction*>& result) const {
	
	Instruction* pRefInstr;
	
	// Iterate over all operands and insert only those in the result set, that
	// are actually instructions
	for(Use const& i : instr.operands()) {
		if((pRefInstr = dyn_cast<Instruction>(&i))) {
			result.insert(pRefInstr);
		}
	}
	
	return result;
}

unordered_set<Instruction*>& PDGPass::getDependencies(
		Instruction const&           instr,
		unordered_set<Instruction*>& result) const {
	
	Instruction* const pCtrlDependency = getCtrlDependency(instr);
	
	// Add data dependencies
	getDataDependencies(instr, result);
	
	// Add control dependency (if present) to the same set
	if(pCtrlDependency) result.insert(pCtrlDependency);
	
	return result;
}

bool PDGPass::runOnFunction(
		Function& func) {
	
	PostDominatorTree const& pdt = getAnalysis<PostDominatorTree>();
	BasicBlock*              pDependency;
	
	// Make sure, the previous state gets forgotten
	_ctrlDependencies.clear();
	
	// Find the control dependency for each basic block 'i'
	for(BasicBlock const& i : func) {
		if((pDependency = computeCtrlDependency(i, pdt))) {
			_ctrlDependencies.insert({{&i, pDependency->getTerminator()}});
		}
	}
	
	return false;
}
