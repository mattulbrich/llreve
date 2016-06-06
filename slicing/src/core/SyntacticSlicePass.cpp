#include "SyntacticSlicePass.h"

#include "SlicingPass.h"
#include "Util.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"

#include <iostream>
#include <queue>

using namespace std;
using namespace llvm;

static RegisterPass<SyntacticSlicePass> tmp(
	"syntactic-slice", "Syntactic Slice", true, false);

char SyntacticSlicePass::ID = 0;

void SyntacticSlicePass::getAnalysisUsage(
		AnalysisUsage &au) const {

	au.addRequiredTransitive<PDGPass>();
}

bool SyntacticSlicePass::runOnFunction(
		Function& func) {

	PDGPass const& pdg = getAnalysis<PDGPass>();

	queue<Instruction const*>         toCheck;
	unordered_set<Instruction const*> remainInSlice;
	unordered_set<Instruction*>       dependencies;

	for(Instruction* i : this->criterion->getInstructions(*func.getParent())) {
		// All criterion instructions must be part of the slice
		toCheck      .push(i);
		remainInSlice.insert(i);
	}

	// Traverse the PDG to find all necessary statements
	while(!toCheck.empty()) {

		Instruction const& curInst = *toCheck.front();
		BasicBlock  const& curBB   = *curInst.getParent();

		// Prepare the basic block's predecessors for dependency checking in
		// future
		for(Instruction const* i : pdg.getDependencies(curInst, dependencies)) {

			BasicBlock     const& depBB    = *i->getParent();
			TerminatorInst const& termInst = *depBB.getTerminator();

			// Check whether instruction is already queued
			if(remainInSlice.find(i) != remainInSlice.end()) {
				continue;
			}

			// Queue the dependency instruction
			toCheck      .push  (i);
			remainInSlice.insert(i);

			// Continue if the current instruction and its dependency are in the
			// same basic block
			if(&curBB == &depBB) {
				continue;
			}

			// Check whether the terminator instruction is already queued
			if(remainInSlice.find(&termInst) != remainInSlice.end()) {
				continue;
			}

			// Also queue the terminator instruction of the dependency
			// instruction's basic block, as the dependency exists between
			// different basic blocks and the connection needs to be kept
			toCheck      .push  (&termInst);
			remainInSlice.insert(&termInst);
		}

		// Unqueue the cuurent instruction and reset its dependencies
		toCheck     .pop();
		dependencies.clear();
	}

	// Mark all instructions, that are not in 'remainInSlice'
	for(Instruction& i : Util::getInstructions(func)) {
		if(remainInSlice.find(&i) == remainInSlice.end()) {
			SlicingPass::toBeSliced(i);;
		}
	}

	return true;
}
