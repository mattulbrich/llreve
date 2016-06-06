#pragma once
#include <memory>
#include "llvm/IR/LegacyPassManager.h"
#include "core/Criterion.h"

class SlicingMethod;
typedef std::shared_ptr<llvm::Module> ModulePtr;
typedef std::shared_ptr<SlicingMethod> SlicingMethodPtr;


class SlicingMethod {
public:
	SlicingMethod(ModulePtr program):program(program){}
	virtual ~SlicingMethod();

	virtual ModulePtr computeSlice(CriterionPtr c) = 0;
	virtual ModulePtr getProgram();

private:
	ModulePtr program;
};
