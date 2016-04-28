#include "llvm/Support/CommandLine.h"
#include "Opts.h"
#include <iostream>


static llvm::cl::opt<std::string> ArgumentFileName(llvm::cl::Positional,
                                           llvm::cl::desc("<input file>"),
                                           llvm::cl::Required);

// Preprocess flags
static llvm::cl::opt<bool> ShowCFGFlag("show-cfg", llvm::cl::desc("Show cfg"),
                                       llvm::cl::cat(ReveCategory));
static llvm::cl::opt<bool>
    ShowMarkedCFGFlag("show-marked-cfg",
                      llvm::cl::desc("Show cfg before mark removal"),
                      llvm::cl::cat(ReveCategory));


int main(int argc, const char **argv) {
	//This lines are here, just to test linking with cmake.
	PreprocessOpts preprocessOpts(ShowCFGFlag, ShowMarkedCFGFlag);
	if (!preprocessOpts.ShowCFG) std::cout << "dont show cfg" << std::endl;

    llvm::cl::ParseCommandLineOptions(argc, argv, "slicing\n");


    return 0;
}
