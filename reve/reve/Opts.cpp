#include "Opts.h"

#include "llvm/Support/CommandLine.h"

using std::string;

llvm::cl::OptionCategory ReveCategory("Reve options",
                                      "Options for controlling reve.");

// Opts for SMT generation
std::string MainFunction;
static llvm::cl::opt<string, true> MainFunctionFlag(
    "fun", llvm::cl::desc("Name of the function which should be verified"),
    llvm::cl::cat(ReveCategory), llvm::cl::location(MainFunction));

bool Heap;
static llvm::cl::opt<bool, true> HeapFlag("heap", llvm::cl::desc("Enable heap"),
                                          llvm::cl::cat(ReveCategory),
                                          llvm::cl::location(Heap));

bool Stack;
static llvm::cl::opt<bool, true> StackFlag("stack",
                                           llvm::cl::desc("Enable stack"),
                                           llvm::cl::cat(ReveCategory),
                                           llvm::cl::location(Stack));

bool GlobalConstants;
static llvm::cl::opt<bool, true>
    GlobalConstantsFlag("strings", llvm::cl::desc("Set global constants"),
                        llvm::cl::cat(ReveCategory),
                        llvm::cl::location(GlobalConstants));

bool OnlyRecursive;
static llvm::cl::opt<bool, true> OnlyRecursiveFlag(
    "only-rec", llvm::cl::desc("Only generate recursive invariants"),
    llvm::cl::cat(ReveCategory), llvm::cl::location(OnlyRecursive));

bool NoByteHeapFlag;
static llvm::cl::opt<bool, true> NoByteHeap(
    "no-byte-heap",
    llvm::cl::desc("Treat each primitive type as a single array entry"),
    llvm::cl::location(NoByteHeapFlag), llvm::cl::cat(ReveCategory));

bool EverythingSignedFlag;
static llvm::cl::opt<bool, true> EverythingSigned(
    "signed", llvm::cl::desc("Treat all operations as signed operatons"),
    llvm::cl::location(EverythingSignedFlag), llvm::cl::cat(ReveCategory));

bool SingleInvariantFlag;
static llvm::cl::opt<bool, true> SingleInvariant(
    "single-invariant",
    llvm::cl::desc("Use a single invariant indexed by the mark"),
    llvm::cl::location(SingleInvariantFlag), llvm::cl::cat(ReveCategory));

bool MuZFlag;
static llvm::cl::opt<bool, true>
    MuZ("muz", llvm::cl::desc("Create smt intended for conversion to muz"),
        llvm::cl::location(MuZFlag), llvm::cl::cat(ReveCategory));

bool PerfectSyncFlag;
static llvm::cl::opt<bool, true> perfectSync(
    "perfect-sync",
    llvm::cl::desc("Perfect synchronization, don’t allow off by n loops"),
    llvm::cl::location(PerfectSyncFlag), llvm::cl::cat(ReveCategory));

bool NestFlag;
static llvm::cl::opt<bool, true>
    nest("nest",
         llvm::cl::desc("Nest clauses, this can sometimes help eldarica"),
         llvm::cl::location(NestFlag), llvm::cl::cat(ReveCategory));

bool PassInputThroughFlag;
static llvm::cl::opt<bool, true>
    PassInputThrough("pass-input-through",
                     llvm::cl::desc("Pass the input arguments through the "
                                    "complete program. This makes it possible "
                                    "to use them in custom postconditions"),
                     llvm::cl::location(PassInputThroughFlag),
                     llvm::cl::cat(ReveCategory));

// Opts for preprocessing
bool ShowCFG;
static llvm::cl::opt<bool, true> ShowCFGFlag("show-cfg",
                                             llvm::cl::desc("Show cfg"),
                                             llvm::cl::cat(ReveCategory),
                                             llvm::cl::location(ShowCFG));
bool ShowMarkedCFG;
static llvm::cl::opt<bool, true> ShowMarkedCFGFlag(
    "show-marked-cfg", llvm::cl::desc("Show cfg before mark removal"),
    llvm::cl::cat(ReveCategory), llvm::cl::location(ShowMarkedCFG));
