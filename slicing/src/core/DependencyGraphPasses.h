/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "DependencyGraph.h"
#include "Util.h"

#include "llvm/ADT/GraphTraits.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class CDGPass :
	public DependencyGraph<llvm::Instruction>, public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	CDGPass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction(llvm::Function &func) override;
	
	NodeType& getRoot(void) const;
	
	private:
	
	void computeDependency(
		llvm::BasicBlock&              bb,
		llvm::PostDominatorTree const& pdt);
};

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class DDGPass :
	public DependencyGraph<llvm::Instruction>, public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	DDGPass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction(llvm::Function &func) override;
	
	private:
	
	void computeDependencies(llvm::Instruction const& inst) const;
};

// Computes the CDG for a function.
// To make the pass work correctly, the SimplifyCFG pass must not be run before.
class PDGPass :
	public DependencyGraph<llvm::Instruction>, public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	PDGPass() : llvm::FunctionPass(ID) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction(llvm::Function &func) override;
	
	NodeType& getRoot(void) const;
};

// GraphTraits specializations for dependency graphs based on instructions

template <> struct llvm::GraphTraits<CDGPass::NodeType*> :
	public GraphTraitsGenericNode<CDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<CDGPass::NodeType*>> :
	public GraphTraitsGenericNodeInverse<CDGPass::NodeType::InnerType> {};

template <> struct llvm::GraphTraits<CDGPass::NodeTypeConst*> :
	public GraphTraitsGenericNode<CDGPass::NodeTypeConst::InnerType> {};

template <> struct llvm::GraphTraits<llvm::Inverse<CDGPass::NodeTypeConst*>> :
	public GraphTraitsGenericNodeInverse<CDGPass::NodeTypeConst::InnerType> {};

// GraphTraits specialization for CDGs
template <> struct llvm::GraphTraits<CDGPass*> :
	public llvm::GraphTraits<CDGPass::NodeType*>,
	public GraphTraitsDependencyGraph<llvm::Instruction> {
	
	static NodeType* getEntryNode(CDGPass* pCDG) {
		return &pCDG->getRoot();
	}
};

// GraphTraits specialization for DDGs
template <> struct llvm::GraphTraits<DDGPass*> :
	public llvm::GraphTraits<DDGPass::NodeType*>,
	public GraphTraitsDependencyGraph<llvm::Instruction> {

	// The entry node is a (pseudo) random node
	static NodeType* getEntryNode(DDGPass* pDDG) {
		return &(*pDDG->begin());
	}
};

// GraphTraits specialization for PDGs
template <> struct llvm::GraphTraits<PDGPass*> :
	public llvm::GraphTraits<PDGPass::NodeType*>,
	public GraphTraitsDependencyGraph<llvm::Instruction> {
	
	static NodeType* getEntryNode(PDGPass* pPDG) {
		return &pPDG->getRoot();
	}
};
