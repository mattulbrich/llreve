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

#include "SmtSolver.h"

class FakeCounterexamples : public SmtSolver {
	
	public:
	
	FakeCounterexamples(int const cexIndex) :
		_cexIndex(cexIndex), _cexCounter(0) {}
		
	virtual ~FakeCounterexamples() {}
	
	virtual SatResult checkSat(std::string smtFilePath, CEXType* pCEX = nullptr);
	
	private:
	
	static unsigned int const cexSizes[1];
	static unsigned int const cexCounts[1];
	static int64_t      const cex0[2][3];
	
	int const _cexIndex;
	int       _cexCounter;
};
