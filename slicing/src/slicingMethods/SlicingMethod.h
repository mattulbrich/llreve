#pragma once
#include <memory>
#include "llvm/IR/LegacyPassManager.h"

class SlicingMethod;
typedef std::shared_ptr<llvm::Module> ModulePtr;
typedef std::shared_ptr<SlicingMethod> SlicingMethodPtr;

class Criterion{
public:
	Criterion();
	bool isReturnValue();

private:
	bool isReturnVal;
};

class SlicingMethod {
public:
	SlicingMethod(ModulePtr program):program(program){}
	virtual ~SlicingMethod();

	virtual ModulePtr computeSlice(Criterion c) = 0;
	virtual ModulePtr getProgram();

private:
	ModulePtr program;
};
