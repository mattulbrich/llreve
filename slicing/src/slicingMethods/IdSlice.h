#pragma once

#include "SlicingMethod.h"

class IdSlicing: public SlicingMethod {
public:
	IdSlicing(ModulePtr program):SlicingMethod(program){}
	virtual ModulePtr computeSlice(CriterionPtr c) override;

};
