#pragma once

enum class ProgramSelection { First, Second, Both };
enum class Program { First, Second };

auto asSelection(Program Prog) -> ProgramSelection;
auto programIndex(Program Prog) -> int;
auto swapProgram(Program Prog) -> Program;
