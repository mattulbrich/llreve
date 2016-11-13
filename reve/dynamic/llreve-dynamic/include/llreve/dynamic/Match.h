#pragma once

#include "llreve/dynamic/Interpreter.h"

namespace llreve {
namespace dynamic {
template <typename T> struct MatchInfo {
    MonoPair<const BlockStep<T> *> steps;
    LoopInfo loopInfo;
    Mark mark;
    MatchInfo(MonoPair<const BlockStep<T> *> steps, LoopInfo loopInfo,
              Mark mark)
        : steps(steps), loopInfo(loopInfo), mark(mark) {}
};

template <typename T> struct CoupledCallInfo {
    MonoPair<const llvm::Function *> functions;
    MonoPair<const BlockStep<T> *> steps;
    MonoPair<VarIntVal> returnValues;
    LoopInfo loopInfo;
    Mark mark;
    CoupledCallInfo(MonoPair<const llvm::Function *> functions,
                    MonoPair<const BlockStep<T> *> steps,
                    MonoPair<VarIntVal> returnValues, LoopInfo loopInfo,
                    Mark mark)
        : functions(functions), steps(steps), returnValues(returnValues),
          loopInfo(loopInfo), mark(mark) {}
};

template <typename T> struct UncoupledCallInfo {
    const llvm::Function *function;
    const BlockStep<T> *step;
    VarIntVal returnValue;
    Mark mark;
    Program prog;
    UncoupledCallInfo(const llvm::Function *function, const BlockStep<T> *step,
                      VarIntVal returnValue, Mark mark, Program prog)
        : function(function), step(step), returnValue(returnValue), mark(mark),
          prog(prog) {}
};
}
}
