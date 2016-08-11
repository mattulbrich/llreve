/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Program.h"

ProgramSelection asSelection(Program prog) {
    return prog == Program::First ? ProgramSelection::First
                                  : ProgramSelection::Second;
}

int programIndex(Program prog) { return prog == Program::First ? 1 : 2; }

Program swapProgram(Program prog) {
    return prog == Program::First ? Program::Second : Program::First;
}

// defaults to first
Program asProgram(ProgramSelection prog) {
    switch (prog) {
    case ProgramSelection::First:
        return Program::First;
    case ProgramSelection::Second:
        return Program::Second;
    case ProgramSelection::Both:
        return Program::First;
    }
}
