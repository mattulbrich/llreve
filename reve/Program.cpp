#include "Program.h"

ProgramSelection asSelection(Program prog) {
    return prog == Program::First ? ProgramSelection::First
                                  : ProgramSelection::Second;
}

int programIndex(Program prog) { return prog == Program::First ? 1 : 2; }

Program swapProgram(Program prog) {
    return prog == Program::First ? Program::Second : Program::First;
}
