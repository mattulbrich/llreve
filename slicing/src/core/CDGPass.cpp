#include "CDGPass.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/Support/Casting.h"

#include <iostream>
#include <queue>
#include <stdexcept>
#include <unordered_set>

using namespace std;
using namespace llvm;

static RegisterPass<CDGPass> tmp("cdg-creation", "CDG Creation", true, true);

char CDGPass::ID = 0;

CDGPass::Iterator CDGPass::begin() {
	
	return Util::createValueIteratorP<MapType>(_nodes.begin());
}

//CDGPass::IteratorConst CDGPass::begin() const {
//	
//}

CDGPass::NodeType* CDGPass::computeCtrlDependency(
		BasicBlock&              bb,
		PostDominatorTree const& pdt) {
	
	queue<BasicBlock*>         toCheck;
	unordered_set<BasicBlock*> markedToCheck;
	
	toCheck.push(&bb);
	
	while(!toCheck.empty()) {
		
		BasicBlock& curBB = *toCheck.front();
		
		toCheck.pop();
		
		// Check whether 'curBB' is the control dependency we're looking for
		if(!pdt.dominates(&bb, &curBB)) {
			return &(*this)[*curBB.getTerminator()];
		}
		
		// Prepare the basic block's predecessors for dependency checking in future
		for(BasicBlock* i : predecessors(&curBB)) {
			if(markedToCheck.find(i) == markedToCheck.end()) {
				toCheck      .push(i);
				markedToCheck.insert(i);
			}
		}
	}
	
	// Instructions that aren't dependent on any other instruction depend on the
	// root node
	return _nodes[nullptr];
}

CDGPass::Iterator CDGPass::end() {
	
	return Util::createValueIteratorP<MapType>(_nodes.end());
}

//CDGPass::IteratorConst CDGPass::end() const {
//	
//}

void CDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<PostDominatorTree>();
}

CDGPass::NodeType& CDGPass::getRoot(void) const {
	
	return *_nodes.at(nullptr);
}

CDGPass::NodeType& CDGPass::operator[](
		Instruction& inst) const {
	
	return *_nodes.at(&inst);
}

CDGPass::NodeTypeConst& CDGPass::operator[](
		Instruction const& inst) const {
	
	return *reinterpret_cast<NodeTypeConst*>(_nodes.at(&inst));
}

bool CDGPass::runOnFunction(
		Function& func) {
	
	PostDominatorTree const& pdt = getAnalysis<PostDominatorTree>();
	NodeType*                pDependency;
	
	// Make sure, the previous state gets forgotten
	for(auto const& i : _nodes) {
		delete i.second;
	}
	_nodes.clear();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		_nodes[&i] = new NodeType(&i);
	}
	_nodes[nullptr] = new NodeType(nullptr); // root node
	
	// Find the control dependency for each basic block 'i'
	for(BasicBlock& i : func) {
		
		if(!(pDependency = computeCtrlDependency(i, pdt))) {
			continue;
		}
		
		for(Instruction& j : i) {
			(*this)[j].predecessors.insert(pDependency);
		}
	}
	
	Util::addSuccessors(*this);
	
	return false;
}
