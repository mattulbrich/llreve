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

#include <string>

enum class ProgramSelection { First, Second, Both };
enum class Program { First, Second };

auto asSelection(Program prog) -> ProgramSelection;
auto programIndex(Program prog) -> int;
auto swapProgram(Program prog) -> Program;
auto asProgram(ProgramSelection prog) -> Program;
auto resultName(Program prog) -> std::string;
