#include "Opts.h"

#include "llvm/Support/CommandLine.h"

using std::string;

llvm::cl::OptionCategory ReveCategory("Reve options",
                                      "Options for controlling reve.");

void SMTGenerationOpts::initialize(std::string mainFunction, bool heap,
                                   bool stack, bool globalConstants,
                                   bool onlyRecursive, bool noByteHeap,
                                   bool everythingSigned, bool singleInvariant,
                                   bool muZ, bool perfectSync, bool nest,
                                   bool passInputThrough) {
    SMTGenerationOpts &i = getInstance();
    i.MainFunction = mainFunction;
    i.Heap = heap;
    i.Stack = stack;
    i.GlobalConstants = globalConstants;
    i.OnlyRecursive = onlyRecursive;
    i.NoByteHeap = noByteHeap;
    i.EverythingSigned = everythingSigned;
    i.SingleInvariant = singleInvariant;
    i.MuZ = muZ;
    i.PerfectSync = perfectSync;
    i.Nest = nest;
    i.PassInputThrough = passInputThrough;
}
