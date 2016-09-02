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

#include "Interpreter.h"
#include "LinearizedFunction.h"
#include "smtSolver/SmtSolver.h"

#include "llvm/ADT/APInt.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Support/raw_ostream.h"

#include <list>
#include <unordered_map>
#include <vector>

class DRM {
	
	public:
	
	friend class DRMCompare;
	
	LinearizedFunction const& linFunc;
	
	DRM(LinearizedFunction const& linFunc, CEXType const& cex);
	~DRM(void);
	
	llvm::APInt const& computeSlice(llvm::APInt const& apriori) const;
	void               print       (llvm::raw_ostream& out) const;
	
	private:
	
	unsigned int  const   _instCount;
	llvm::APInt** const   _matrix;
	llvm::APInt   mutable _accumulator;
	
	static llvm::APInt const* findNode(
		std::list<llvm::APInt const*> const& elements,
		llvm::APInt                   const& ref);
	
	void printReachability(
		llvm::APInt const& row,
		llvm::raw_ostream& out) const;
};

class DRMCompare {
	
	public:
	
	// Comparison is defined as lexicographical comparison of the rows
	bool operator() (DRM const& lhs, DRM const& rhs) const;
};

class APIntCompare {
	
	public:
	
	bool operator() (llvm::APInt const& lhs, llvm::APInt const& rhs) const;
};

class CtrlDepExtractionPass : public llvm::FunctionPass {
	
	public:
	
	static char ID;
	
	CtrlDepExtractionPass(
			LinearizedFunction const& linFunc,
			llvm::Instruction  const* dependencies[]) :
		llvm::FunctionPass(ID),
		_linFunc          (linFunc),
		_dependencies     (dependencies) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction   (llvm::Function      &func)     override;
	
	private:
	
	LinearizedFunction        const& _linFunc;
	llvm::Instruction const** const  _dependencies;
};
