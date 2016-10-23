#pragma once

#ifndef _WIN32
#include <unistd.h>
#endif

#include "llvm/Support/raw_ostream.h"

#define logError(Message) logError_(Message, __FILE__, __LINE__)
#define logWarning(Message) logWarning_(Message, __FILE__, __LINE__)
#define logErrorData(Message, El) logErrorData_(Message, El, __FILE__, __LINE__)
#define logWarningData(Message, El)                                            \
    logWarningData_(Message, El, __FILE__, __LINE__)

template <typename Str>
auto logError_(Str message, const char *file, int line) -> void {
    bool colors = false;
#ifndef _WIN32
    colors = isatty(fileno(stderr));
#endif
    if (colors) {
        llvm::errs() << "\x1b[31;1mERROR\x1b[0m\x1b[1m (" << file << ":" << line
                     << "): " << message << "\x1b[0m";
    } else {
        llvm::errs() << "ERROR: " << message;
    }
}

template <typename Str>
auto logWarning_(Str message, const char *file, int line) -> void {
    bool colors = false;
#ifndef _WIN32
    colors = isatty(fileno(stderr));
#endif
    if (colors) {
        llvm::errs() << "\x1b[33;1mWARNING\x1b[0m\x1b[1m (" << file << ":"
                     << line << "): " << message << "\x1b[0m";
    } else {
        llvm::errs() << "WARNING: " << message;
    }
}

template <typename Str, typename A>
auto logErrorData_(Str message, A &el, const char *file, int line) -> void {
    logError_(message, file, line);
    el.print(llvm::errs());
    llvm::errs() << "\n";
}

template <typename Str, typename A>
auto logWarningData_(Str message, A &el, const char *file, int line) -> void {
    logWarning_(message, file, line);
    el.print(llvm::errs());
    llvm::errs() << "\n";
}
