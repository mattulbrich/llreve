#pragma once

#include "SlicingMethod.h"

class SingleLineElimination: public SlicingMethod {
public:
	SingleLineElimination(ModulePtr program):SlicingMethod(program){}
	virtual ModulePtr computeSlice(CriterionPtr c) override;

};
