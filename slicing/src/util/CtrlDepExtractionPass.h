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

#include "dynamic/LinearizedFunction.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"

#include <vector>

class CtrlDepExtractionPass : public llvm::FunctionPass {
	
	public:
	
	typedef std::vector<llvm::Instruction const*> ResultType;
	
	static char ID;
	
	CtrlDepExtractionPass(
			LinearizedFunction const& linFunc,
			ResultType&               dependencies) :
		llvm::FunctionPass(ID),
		_linFunc          (linFunc),
		_dependencies     (dependencies) {}
	
	virtual void getAnalysisUsage(llvm::AnalysisUsage &au) const override;
	virtual bool runOnFunction   (llvm::Function      &func)     override;
	
	static ResultType  getCtrlDependencies(
		LinearizedFunction const& linFunc);
	static ResultType& getCtrlDependencies(
		LinearizedFunction const& linFunc,
		ResultType&               result);
	
	private:
	
	LinearizedFunction const& _linFunc;
	ResultType&               _dependencies;
};
