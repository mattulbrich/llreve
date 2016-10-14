#pragma once

#include "Preprocess.h"

auto relationalFunctionDeclarations(
    MonoPair<PreprocessedFunction> preprocessedFunctions)
    -> std::vector<smt::SharedSMTRef>;
auto functionalFunctionDeclarations(PreprocessedFunction preprocessedFunction,
                                    Program program)
    -> std::vector<smt::SharedSMTRef>;

auto relationalIterativeDeclarations(
    MonoPair<PreprocessedFunction> preprocessedFunctions)
    -> std::vector<smt::SharedSMTRef>;
