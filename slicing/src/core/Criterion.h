#pragma once

#include "llvm/IR/Instruction.h"
#include <set>

enum class CriterionConstructionOption{returnValue, present};

class Criterion;

typedef std::shared_ptr<Criterion> CriterionPtr;

class Criterion{
public:
	Criterion();
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
