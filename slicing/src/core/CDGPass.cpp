#include "CDGPass.h"

#include "llvm/IR/CFG.h"

#include <iostream>
#include <queue>
#include <unordered_set>

using namespace std;
using namespace llvm;

static RegisterPass<CDGPass> tmp("cdg-creation", "CDG Creation", true, true);

char CDGPass::ID = 0;

CDGPass::~CDGPass() {
	
	clearNodes();
}

CDGPass::Iterator CDGPass::begin() {
	
	return Util::createValueIteratorP<MapType>(_nodes.begin());
}

//CDGPass::IteratorConst CDGPass::begin() const {
//	
//}

void CDGPass::clearNodes(void) {
	
	for(auto const& i : _nodes) {
		delete i.second;
	}
	
	_nodes.clear();
} 

void CDGPass::computeDependency(
		BasicBlock&              bb,
		PostDominatorTree const& pdt) {
	
	NodeType*                  pDependency = &getRoot();
	queue<BasicBlock*>         toCheck;
	unordered_set<BasicBlock*> markedToCheck;
	
	toCheck.push(&bb);
	
	while(!toCheck.empty()) {
		
		BasicBlock& curBB = *toCheck.front();
		
		toCheck.pop();
		
		// Check whether 'curBB' is the control dependency we're looking for
		if(!pdt.dominates(&bb, &curBB)) {
			pDependency = &(*this)[*curBB.getTerminator()];
			break;
		}
		
		// Prepare the basic block's predecessors for dependency checking in future
		for(BasicBlock* i : predecessors(&curBB)) {
			if(markedToCheck.find(i) == markedToCheck.end()) {
				toCheck      .push(i);
				markedToCheck.insert(i);
			}
		}
	}
	
	// All instructions in a basic block share the same control dependency
	for(Instruction& i : bb) {
		(*this)[i].predecessors.insert(pDependency);
	}
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
	
	// Make sure, the previous state gets forgotten
	clearNodes();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		_nodes[&i] = new NodeType(&i);
	}
	_nodes[nullptr] = new NodeType(nullptr); // root node
	
	// Find the control dependency for each basic block 'i'
	for(BasicBlock& i : func) {
		computeDependency(i, pdt);
	}
	
	// Complete the graph
	Util::addSuccessors(*this);
	
	return false;
}
