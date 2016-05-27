#pragma once

#include "SlicingMethod.h"


class BruteForce: public SlicingMethod {
public:
	BruteForce(ModulePtr program):SlicingMethod(program){}
	virtual ModulePtr computeSlice(Criterion c) override;
};
