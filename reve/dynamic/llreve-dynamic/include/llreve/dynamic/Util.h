#pragma once

#include "SMT.h"

namespace llreve {
namespace dynamic {
std::vector<smt::SortedVar>
removeHeapVariables(const std::vector<smt::SortedVar> &freeVariables);

std::vector<std::vector<std::string>>
polynomialTermsOfDegree(std::vector<smt::SortedVar> variables, size_t degree);
}
}
