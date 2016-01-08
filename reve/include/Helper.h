#ifndef HELPER_H
#define HELPER_H

#include <string>

#include <unistd.h>
#include "llvm/Support/raw_ostream.h"

template <typename Str> auto logError(Str Message) -> void {
    if (isatty(fileno(stdout))) {
        llvm::errs() << "\x1b[31;1mERROR:\x1b[0m\x1b[1m " << Message << "\x1b[0m";
    } else {
        llvm::errs() << "ERROR: " << Message;
    }
}

template <typename Str> auto logWarning(Str Message) -> void {
    if (isatty(fileno(stdout))) {
        llvm::errs() << "\x1b[33;2mWARNING:\x1b[0m\x1b[1m " << Message << "\x1b[0m";
    } else {
        llvm::errs() << "WARNING: " << Message;
    }
}

template <typename Str, typename A> auto logErrorData(Str Message, A& El) -> void {
    logError(Message);
    El.print(llvm::errs());
    llvm::errs() << "\n";
}

template <typename Str, typename A> auto logWarningData(Str Message, A& El) -> void {
    logWarning(Message);
    El.print(llvm::errs());
    llvm::errs() << "\n";
}

#endif // HELPER_H
