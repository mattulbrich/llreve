/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#pragma once

#include "MonoPair.h"
#include "SMT.h"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include <map>

extern llvm::cl::OptionCategory ReveCategory;

/// Options used for preprocessing modules
class PreprocessOpts {
  public:
    bool ShowCFG;
    bool ShowMarkedCFG;
    bool InferMarks;
    PreprocessOpts(bool showCFG, bool showMarkedCFG, bool inferMarks)
        : ShowCFG(showCFG), ShowMarkedCFG(showMarkedCFG),
          InferMarks(inferMarks) {}
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
    static void
    initialize(std::string mainFunction, bool heap, bool stack,
               bool globalConstants, bool onlyRecursive, bool noByteHeap,
               bool everythingSigned, bool muZ, bool perfectSync,
               bool passInputThrough, bool bitvect, bool invert,
               bool initPredicate, bool disableAutoAbstraction,
               std::map<int, smt::SharedSMTRef> invariants,
               std::set<MonoPair<const llvm::Function *>> assumeEquivalent,
               std::set<MonoPair<llvm::Function *>> coupleFunctions);
    std::string MainFunction;
    bool Heap;
    bool Stack;
    bool GlobalConstants;
    bool OnlyRecursive;
    bool NoByteHeap;
    bool EverythingSigned;
    bool MuZ;
    bool PerfectSync;
    bool PassInputThrough;
    bool BitVect;
    bool Invert;
    bool InitPredicate;
    bool DisableAutoAbstraction;
    // If an invariant is not in the map a declaration is added and it’s up to
    // the SMT solver to find it
    std::map<int, smt::SharedSMTRef> Invariants;
    std::set<MonoPair<const llvm::Function *>> AssumeEquivalent;
    // The order in the pairs is normalized so that the first function is always
    // in the first module.
    std::set<MonoPair<llvm::Function *>> CoupledFunctions;

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
    bool DontInstantiate;
    bool MergeImplications;
    bool RenameDefineFuns;
    bool Pretty;
    SerializeOpts(std::string outputFileName, bool DontInstantiate,
                  bool MergeImplications, bool RenameDefineFuns, bool Pretty)
        : OutputFileName(outputFileName), DontInstantiate(DontInstantiate),
          MergeImplications(MergeImplications),
          RenameDefineFuns(RenameDefineFuns), Pretty(Pretty) {}
};

/// Options that are parsed from special comments inside the programs
/// Currently this consists of custom relations and preconditions
class FileOptions {
  public:
    // map from function names to conditions
    std::multimap<std::string, std::string> FunctionConditions;
    smt::SharedSMTRef InRelation;
    smt::SharedSMTRef OutRelation;
    // Indicates if InRelation is meant to replace the existing relation or just
    // enhance it
    bool AdditionalInRelation;
    FileOptions(std::multimap<std::string, std::string> functionConditions,
                smt::SharedSMTRef inRelation, smt::SharedSMTRef outRelation,
                bool additionalIn)
        : FunctionConditions(functionConditions), InRelation(inRelation),
          OutRelation(outRelation), AdditionalInRelation(additionalIn) {}
};

/// If inline-opts is passed this will try to read arguments from the files.
/// In that case the files have to come before any other option that takes an
/// argument.
auto parseCommandLineArguments(int argc, const char **argv) -> void;

// Search for command line options that are specified inside the programs
auto getInlineOpts(const char *file1, const char *file2)
    -> std::vector<std::string>;

// Search for options that can only be specified as special comments inside the
// programs
auto getFileOptions(MonoPair<std::string> fileNames) -> FileOptions;

auto searchCustomRelations(MonoPair<std::string> fileNames, bool &additionalIn)
    -> MonoPair<smt::SharedSMTRef>;
auto searchCustomRelationsInFile(std::string file, smt::SharedSMTRef &in,
                                 smt::SharedSMTRef &out, bool &additionalIn)
    -> void;
auto searchFunctionConditions(MonoPair<std::string> fileNames)
    -> std::multimap<std::string, std::string>;
auto searchFunctionConditionsInFile(std::string file)
    -> std::multimap<std::string, std::string>;
auto parseFunctionPairFlags(llvm::cl::list<std::string> &functionPairFlag)
    -> std::set<MonoPair<std::string>>;
// Depending on the value of disableAutoCoupling this will infer functions to be
// coupled based on their name or use the function names in the
// `coupledFunctionNames`
auto getCoupledFunctions(MonoPair<std::shared_ptr<llvm::Module>> modules,
                         bool disableAutoCoupling,
                         std::set<MonoPair<std::string>> coupledFunctionNames)
    -> std::set<MonoPair<llvm::Function *>>;
auto inferCoupledFunctionsByName(
    MonoPair<std::shared_ptr<llvm::Module>> modules)
    -> std::set<MonoPair<llvm::Function *>>;
// This function will exit the program if it fails so only use this for input
// validation
auto lookupFunctionNamePairs(
    MonoPair<std::shared_ptr<llvm::Module>> modules,
    std::set<MonoPair<std::string>> coupledFunctionNames)
    -> std::set<MonoPair<llvm::Function *>>;
auto isPartOfEquivalence(const llvm::Function &f) -> bool;

bool isLlreveIntrinsic(const llvm::Function &);
bool hasMutualFixedAbstraction(MonoPair<const llvm::Function *> functions);
bool hasFixedAbstraction(const llvm::Function &function);
auto addConstToFunctionPairSet(
    std::set<MonoPair<llvm::Function *>> functionPairs)
    -> std::set<MonoPair<const llvm::Function *>>;
