// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "SyntacticSlicePass.h"

#include "SlicingPass.h"
#include "Util.h"

#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"

#include <iostream>
#include <queue>
#include <set>

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

	set<Instruction*>                         initInstructions = criterion->getInstructions(*func.getParent());
	unordered_set<GenericNode<Instruction*>*> remainInSlice;
	
	pdg.getInfluencingNodes(initInstructions, remainInSlice);
	
	// Mark all instructions, that are not in 'remainInSlice'
	for(Instruction& i : Util::getInstructions(func)) {
		if(remainInSlice.find(&pdg[i]) == remainInSlice.end()) {
			SlicingPass::toBeSliced(i);
		}
	}

	return true;
}
