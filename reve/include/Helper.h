#pragma once

#include "SMT.h"

#include <string>

#include <unistd.h>
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"

#define logError(Message) logError_(Message, __FILE__, __LINE__)
#define logWarning(Message) logWarning_(Message, __FILE__, __LINE__)
#define logErrorData(Message, El) logErrorData_(Message, El, __FILE__, __LINE__)
#define logWarningData(Message, El)                                            \
    logWarningData_(Message, El, __FILE__, __LINE__)

template <typename Str>
auto logError_(Str Message, const char *File, int Line) -> void {
    if (isatty(fileno(stdout))) {
        llvm::errs() << "\x1b[31;1mERROR\x1b[0m\x1b[1m (" << File << ":" << Line
                     << "): " << Message << "\x1b[0m";
    } else {
        llvm::errs() << "ERROR: " << Message;
    }
}

template <typename Str>
auto logWarning_(Str Message, const char *File, int Line) -> void {
    if (isatty(fileno(stdout))) {
        llvm::errs() << "\x1b[33;1mWARNING\x1b[0m\x1b[1m (" << File << ":"
                     << Line << "): " << Message << "\x1b[0m";
    } else {
        llvm::errs() << "WARNING: " << Message;
    }
}

template <typename Str, typename A>
auto logErrorData_(Str Message, A &El, const char *File, int Line) -> void {
    logError_(Message, File, Line);
    El.print(llvm::errs());
    llvm::errs() << "\n";
}

template <typename Str, typename A>
auto logWarningData_(Str Message, A &El, const char *File, int Line) -> void {
    logWarning_(Message, File, Line);
    El.print(llvm::errs());
    llvm::errs() << "\n";
}

auto resolveName(const std::string Name,
                 const std::set<std::string> Constructed) -> std::string;
