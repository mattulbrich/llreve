#pragma once

#include "slicingMethods/SlicingMethod.h"

class ImpactAnalysisForAssignments: public SlicingMethod {
public:
	static std::string EVERY_VALUE_FUNCTION_NAME;
	/**
	 * @param program to slice
	 */
	ImpactAnalysisForAssignments(ModulePtr program);
	virtual ModulePtr computeSlice(CriterionPtr c) override;

private:
	llvm::Function* createEveryValueFunction(ModulePtr impactAbstraction, llvm::Type* type = nullptr);
};
