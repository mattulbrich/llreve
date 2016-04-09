#pragma once

#include "MonoPair.h"
#include "llvm/Support/CommandLine.h"

extern llvm::cl::OptionCategory ReveCategory;

/// Options used for preprocessing modules
class PreprocessOpts {
  public:
    bool ShowCFG;
    bool ShowMarkedCFG;
    PreprocessOpts(bool showCFG, bool showMarkedCFG)
        : ShowCFG(showCFG), ShowMarkedCFG(showMarkedCFG) {}
};

/// Singleton for the options used for SMT generation to avoid having to pass
/// around the config object
class SMTGenerationOpts {
  public:
    static SMTGenerationOpts &getInstance() {
        static SMTGenerationOpts instance;
        return instance;
    }
    // Convenience method to make sure you don’t forget to set parameters
    static void initialize(std::string mainFunction, bool heap, bool stack,
                           bool globalConstants, bool onlyRecursive,
                           bool noByteHeap, bool everythingSigned,
                           bool singleInvariant, bool muZ, bool perfectSync,
                           bool nest, bool passInputThrough);
    std::string MainFunction;
    bool Heap;
    bool Stack;
    bool GlobalConstants;
    bool OnlyRecursive;
    bool NoByteHeap;
    bool EverythingSigned;
    bool SingleInvariant;
    bool MuZ;
    bool PerfectSync;
    bool Nest;
    bool PassInputThrough;

  private:
    SMTGenerationOpts() {}
    SMTGenerationOpts(SMTGenerationOpts const &) = delete;
    void operator=(SMTGenerationOpts const &) = delete;
};

/// Options used for reading the C source and compiling it to llvm modules
class InputOpts {
  public:
    std::vector<std::string> Includes;
    std::string ResourceDir;
    MonoPair<std::string> FileNames;
    InputOpts(std::vector<std::string> includes, std::string resourceDir,
              std::string file1, std::string file2)
        : Includes(includes), ResourceDir(resourceDir),
          FileNames(makeMonoPair(file1, file2)) {}
};

/// Options used for serializing the SMT
class SerializeOpts {
  public:
    std::string OutputFileName;
    SerializeOpts(std::string outputFileName)
        : OutputFileName(outputFileName) {}
};
