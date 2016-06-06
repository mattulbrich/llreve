#pragma once

#include "SlicingMethod.h"

class SyntacticSlicing: public SlicingMethod {
public:
	SyntacticSlicing(ModulePtr program):SlicingMethod(program){}
	virtual ModulePtr computeSlice(CriterionPtr c) override;

};
