#include "FakeCounterexamples.h"

using namespace std;

unsigned int const FakeCounterexamples::cexSizes [1] = {3};
unsigned int const FakeCounterexamples::cexCounts[1] = {2};

int64_t const FakeCounterexamples::cex0[2][3] = {{0, 1, 0}, {0, 1, 1}};

SatResult FakeCounterexamples::checkSat(
		string   smtFilePath,
		CEXType* pCEX) {
	
	if(_cexCounter == cexCounts[_cexIndex]) {
		
		return SatResult::sat;
		
	} else {
		
		unsigned int   const cexSize  = cexSizes[_cexIndex];
		int64_t const* const pFakeCex = cex0    [_cexCounter];
		
		for(unsigned int i = 0; i < cexSize; i++) {
			(*pCEX)[i] = pFakeCex[i];
		}
		
		_cexCounter++;
		
		return SatResult::unsat;
	}
}
