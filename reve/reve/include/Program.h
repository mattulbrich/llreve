#pragma once

enum class ProgramSelection { First, Second, Both };
enum class Program { First, Second };

auto asSelection(Program prog) -> ProgramSelection;
auto programIndex(Program prog) -> int;
auto swapProgram(Program prog) -> Program;
