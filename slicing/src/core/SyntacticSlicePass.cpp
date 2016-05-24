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
	
	for(Instruction& i : Util::getInstructions(func)) {
		// All return instructions must be part of the slice
		if(isa<ReturnInst>(&i)) {
			toCheck      .push(&i);
			remainInSlice.insert(&i);
		}
	}
	
	while(!toCheck.empty()) {
		
		// Prepare the basic block's predecessors for dependency checking in future
		for(Instruction const* i :
			pdg.getDependencies(*toCheck.front(), dependencies)) {
			
			if(remainInSlice.find(i) == remainInSlice.end()) {
				toCheck      .push(i);
				remainInSlice.insert(i);
			}
		}
		
		toCheck.pop();
	}
	
	for(Instruction& i : Util::getInstructions(func)) {
		if(remainInSlice.find(&i) == remainInSlice.end()) {
			SlicingPass::toBeSliced(i);;
		}
	}
	
	return true;
}
