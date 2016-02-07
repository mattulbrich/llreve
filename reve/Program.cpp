#include "Program.h"

ProgramSelection asSelection(Program Prog) {
    return Prog == Program::First ? ProgramSelection::First
                                  : ProgramSelection::Second;
}

int programIndex(Program Prog) { return Prog == Program::First ? 1 : 2; }

Program swapProgram(Program Prog) {
    return Prog == Program::First ? Program::Second : Program::First;
}
