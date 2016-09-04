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

#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"

#include <unordered_map>

class LinearizedFunction {
	
	public:
	
	llvm::Function const& func;
	
	LinearizedFunction(llvm::Function const& func);
	~LinearizedFunction(void);
	
	unsigned int getInstructionCount(void)     const;
	void         print(llvm::raw_ostream& out) const;
	std::string  indexToString(unsigned int const index) const;
	
	llvm::Instruction const& operator[](unsigned int const       index) const;
	unsigned int             operator[](llvm::Instruction const& inst)  const;
	
	private:
	
	unsigned int _printPaddingLength;
	
	std::unordered_map<llvm::Instruction const*, unsigned int> _mapInstToInt;
	llvm::Instruction const**                                  _mapIntToInst;
};
