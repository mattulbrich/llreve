#include "Helper.h"

#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <unistd.h>

void logError(std::string Message) {
    if (isatty(fileno(stdout))) {
        llvm::errs() << "\x1b[31mERROR:\x1b[0m \x1b[1m" << Message << "\x1b[0m\n";
    } else {
        llvm::errs() << "ERROR: " << Message << "\n";
    }
}
