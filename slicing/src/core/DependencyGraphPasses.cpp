/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

// *** ADDED BY HEADER FIXUP ***
#include <istream>
// *** END ***
#include "DependencyGraphPasses.h"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Use.h"
#include "llvm/Support/Casting.h"

#include <iostream>

using namespace std;
using namespace llvm;

// Member definition for the CDG pass

static RegisterPass<CDGPass> tmpCDG("cdg-creation", "CDG Creation", true, true);

char CDGPass::ID = 0;

void CDGPass::computeDependency(
		BasicBlock&              bb,
		PostDominatorTree const& pdt) {
	
	unordered_set<NodeType*>   dependencies;
	queue<BasicBlock*>         toCheck;
	unordered_set<BasicBlock*> markedToCheck;
	
	toCheck.push(&bb);
	
	while(!toCheck.empty()) {
		
		BasicBlock& curBB = *toCheck.front();
		
		toCheck.pop();
		
		// Check whether 'curBB' is a control dependency (there may be multiple)
		if(!pdt.dominates(&bb, &curBB)) {
			
			dependencies.insert(&(*this)[*curBB.getTerminator()]);
			
		} else {
		
			// Prepare the basic block's predecessors for dependency checking in
			// future
			for(BasicBlock* i : predecessors(&curBB)) {
				if(markedToCheck.find(i) == markedToCheck.end()) {
					toCheck      .push(i);
					markedToCheck.insert(i);
				}
			}
		}
	}
	
	// If there are no dependencies, set the root node as dependency
	if(dependencies.empty()) {
		dependencies.insert(&getRoot());
	}
	
	// All instructions in a basic block share the same control dependencies
	for(Instruction& i : bb) {
		for(NodeType* const j : dependencies) {
			(*this)[i].predecessors.insert(j);
		}
	}
}

void CDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<PostDominatorTree>();
}

CDGPass::NodeType& CDGPass::getRoot(void) const {
	
	return (*this)[nullptr];
}

bool CDGPass::runOnFunction(
		Function& func) {
	
	PostDominatorTree const& pdt = getAnalysis<PostDominatorTree>();
	
	// Make sure, the previous state gets forgotten
	clearNodes();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		createNode(&i);
	}
	createNode(nullptr); // root node
	
	// Find the control dependency for each basic block 'i'
	for(BasicBlock& i : func) {
		computeDependency(i, pdt);
	}
	
	// Complete the graph
	Util::addSuccessors(*this);
	
	return false;
}

// Member definition for the DDG pass

static RegisterPass<DDGPass> tmpDDG("ddg-creation", "DDG Creation", true, true);

char DDGPass::ID = 0;

void DDGPass::computeDependencies(
		Instruction const& inst) const {
	
	NodeTypeConst&     instNode = (*this)[inst];
	Instruction const* pRefInst;
	
	// Iterate over all operands and insert only those in the predecessor set,
	// that are actually instructions
	for(Use const& i : inst.operands()) {
		if((pRefInst = dyn_cast<Instruction const>(&i))) {
			instNode.predecessors.insert(&(*this)[*pRefInst]);
		}
	}
	
	if(isa<LoadInst>(&inst)) {
		
		SingeltonQueue<BasicBlock const*> toCheck(true);
		unordered_set<StoreInst const*>   heapDependencies;
		
		toCheck.push(inst.getParent());
		
		while(!toCheck.empty()) {
			
			BasicBlock const& curBB = *toCheck.pop();
			
			getStoreInstructions(curBB, inst, heapDependencies);
			
			for(BasicBlock const* i : predecessors(&curBB)) {
				toCheck.push(i);
			}
		}
		
		for(StoreInst const* const i : heapDependencies) {
			instNode.predecessors.insert(&(*this)[*i]);
		}
	}
}

void DDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
}

void DDGPass::getStoreInstructions(
		BasicBlock  const&               bb,
		Instruction const&               abortInst,
		unordered_set<StoreInst const*>& result) const {
	
	for(Instruction const& i : bb) {
		
		if(StoreInst const* pStoreInst = dyn_cast<StoreInst>(&i)) {
			result.insert(pStoreInst);
		}
		
		if(&i == &abortInst) {
			break;
		}
	}
}

bool DDGPass::runOnFunction(
		Function& func) {
	
	// Make sure, the previous state gets forgotten
	clearNodes();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		createNode(&i);
	}
	
	// Compute the data dependencies for each instruction
	for(Instruction const& i : Util::getInstructions(func)) {
		computeDependencies(i);
	}
	
	// Complete the graph
	Util::addSuccessors(*this);
	
	return false;
}

// Member definition for the PDG pass

static RegisterPass<PDGPass> tmpPDG("pdg-creation", "PDG Creation", true, true);

char PDGPass::ID = 0;

void PDGPass::getAnalysisUsage(
		AnalysisUsage &au) const {
	
	au.setPreservesAll();
	au.addRequiredTransitive<CDGPass>();
	au.addRequiredTransitive<DDGPass>();
}

PDGPass::NodeType& PDGPass::getRoot(void) const {
	
	return (*this)[nullptr];
}

bool PDGPass::runOnFunction(
		Function& func) {
	
	CDGPass const& cdg = getAnalysis<CDGPass>();
	DDGPass const& ddg = getAnalysis<DDGPass>();
	
	// Make sure, the previous state gets forgotten
	clearNodes();
	
	// Create a generic node for each instruction and store the mapping
	for(Instruction& i : Util::getInstructions(func)) {
		createNode(&i);
	}
	createNode(nullptr); // root node
	
	for(Instruction& i : Util::getInstructions(func)) {
		
		NodeType& node    = (*this)[i];
		NodeType& nodeCDG = cdg[i];
		NodeType& nodeDDG = ddg[i];
		
		// Combine the predecessors of both CDG and DDG
		for(auto j : nodeCDG.predecessors) {
			node.predecessors.insert(&(*this)[j->innerNode]);
		}
		for(auto j : nodeDDG.predecessors) {
			node.predecessors.insert(&(*this)[j->innerNode]);
		}
	}
	
	// Complete the graph
	Util::addSuccessors(*this);
	
	return false;
}
