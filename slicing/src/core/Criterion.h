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

#include "llvm/IR/Instruction.h"
#include <set>

enum class CriterionConstructionOption{returnValue, present};

class Criterion;

typedef std::shared_ptr<Criterion> CriterionPtr;

class Criterion{
public:
	Criterion();
	static const std::string FUNCTION_NAME;
	virtual bool isReturnValue() const;
	virtual std::set<llvm::Instruction*> getInstructions(llvm::Module& module) const = 0;
	virtual ~Criterion() = default;
	static CriterionPtr getReturnValueCriterion();
};


class ReturnValueCriterion: public Criterion {
public:
	ReturnValueCriterion();
	virtual ~ReturnValueCriterion() = default;
	virtual bool isReturnValue() const;
	virtual std::set<llvm::Instruction*> getInstructions(llvm::Module& module) const;
};

class PresentCriterion: public Criterion {
public:
	PresentCriterion();
	virtual ~PresentCriterion() = default;
	virtual std::set<llvm::Instruction*> getInstructions(llvm::Module& module) const;
};
