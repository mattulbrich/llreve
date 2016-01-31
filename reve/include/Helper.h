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

auto instrNameOrVal(const llvm::Value *Val, const llvm::Type *Ty) -> SMTRef;
auto typeSize(llvm::Type *Ty) -> int;
template <typename T> SMTRef resolveGEP(T &GEP) {
    std::vector<SMTRef> Args;
    Args.push_back(instrNameOrVal(GEP.getPointerOperand(),
                                  GEP.getPointerOperand()->getType()));
    const auto Type = GEP.getSourceElementType();
    std::vector<llvm::Value *> Indices;
    for (auto Ix = GEP.idx_begin(), E = GEP.idx_end(); Ix != E; ++Ix) {
        Indices.push_back(*Ix);
        const auto Size = typeSize(llvm::GetElementPtrInst::getIndexedType(
            Type, llvm::ArrayRef<llvm::Value *>(Indices)));
        if (Size == 1) {
            Args.push_back(instrNameOrVal(*Ix, (*Ix)->getType()));
        } else {
            Args.push_back(makeBinOp("*", name(std::to_string(Size)),
                                     instrNameOrVal(*Ix, (*Ix)->getType())));
        }
    }
    return std::make_shared<Op>("+", Args);
}
