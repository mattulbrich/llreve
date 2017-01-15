/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Opts.h"
#include "Helper.h"
#include "SMT.h"

#include <fstream>
#include <regex>

using std::shared_ptr;
using std::map;
using std::set;
using std::string;
using std::vector;
using smt::stringExpr;
using smt::SharedSMTRef;

namespace llreve {
namespace opts {
llreve::cl::OptionCategory ReveCategory("Reve options",
                                        "Options for controlling reve.");

void SMTGenerationOpts::initialize(
    MonoPair<llvm::Function *> mainFunctions, enum HeapOpt heap,
    enum StackOpt stack, enum GlobalConstantsOpt globalConstants,
    FunctionEncoding onlyRecursive, enum ByteHeapOpt byteHeap,
    bool everythingSigned, SMTFormat muZ,
    enum PerfectSynchronization perfectSync, bool passInputThrough,
    bool bitVect, bool invert, bool initPredicate, bool disableAutoAbstraction,
    map<Mark, SharedSMTRef> iterativeRelationalInvariants,
    map<const llvm::Function *, map<Mark, FunctionInvariant<SharedSMTRef>>>
        functionalFunctionalInvariants,
    map<MonoPair<const llvm::Function *>,
        map<Mark, FunctionInvariant<SharedSMTRef>>>
        functionalRelationalInvariants,
    set<MonoPair<const llvm::Function *>> assumeEquivalent,
    set<MonoPair<llvm::Function *>> coupledFunctions,
    map<const llvm::Function *, int> functionNumerals,
    MonoPair<map<int, const llvm::Function *>> reversedFunctionNumerals) {
    SMTGenerationOpts &i = getInstance();
    i.MainFunctions = mainFunctions;
    i.Heap = heap;
    i.Stack = stack;
    i.GlobalConstants = globalConstants;
    i.OnlyRecursive = onlyRecursive;
    i.ByteHeap = byteHeap;
    i.EverythingSigned = everythingSigned;
    i.OutputFormat = muZ;
    i.PerfectSync = perfectSync;
    i.PassInputThrough = passInputThrough;
    i.BitVect = bitVect;
    i.InitPredicate = initPredicate;
    i.DisableAutoAbstraction = disableAutoAbstraction;
    i.IterativeRelationalInvariants = iterativeRelationalInvariants;
    i.FunctionalFunctionalInvariants = functionalFunctionalInvariants;
    i.FunctionalRelationalInvariants = functionalRelationalInvariants;
    i.Invert = invert;
    i.AssumeEquivalent = assumeEquivalent;
    i.CoupledFunctions = coupledFunctions;
    i.FunctionNumerals = functionNumerals;
    i.ReversedFunctionNumerals = reversedFunctionNumerals;
}

void parseCommandLineArguments(int argc, const char **argv) {
    llreve::cl::HideUnrelatedOptions(ReveCategory);
    bool inlineOpts = false;
    // We can’t use the option parser for this since it can only be run once
    // (global state, fuck yeah) and
    // we might want to add arguments to it
    const char *file1 = nullptr;
    const char *file2 = nullptr;
    for (int i = 1; i < argc; ++i) {
        if (*argv[i] != '-') {
            if (!file1) {
                file1 = argv[i];
            } else if (!file2) {
                file2 = argv[i];
            }
        } else if (strcmp(argv[i], "-inline-opts") == 0) {
            inlineOpts = true;
        }
    }
    if (inlineOpts) {
        const vector<std::string> parsedOpts = getInlineOpts(file1, file2);
        vector<const char *> parsedOptsCStyle;
        for (int i = 0; i < argc; ++i) {
            if (strcmp(argv[i], "-inline-opts") != 0) {
                parsedOptsCStyle.push_back(argv[i]);
            }
        }
        for (const string &opt : parsedOpts) {
            parsedOptsCStyle.push_back(opt.c_str());
        }
        argc = static_cast<int>(parsedOptsCStyle.size());
        argv = &parsedOptsCStyle[0];
        llreve::cl::ParseCommandLineOptions(argc, argv, "reve\n");
    } else {
        llreve::cl::ParseCommandLineOptions(argc, argv, "reve\n");
    }
}

std::vector<string> getInlineOpts(const char *file1, const char *file2) {
    std::regex optRegex("/\\*@\\s*opt\\s+(\\S+)\\s+(\\S*)\\s*@\\*/",
                        std::regex::ECMAScript);
    std::vector<string> args;
    makeMonoPair(file1, file2).forEach([&args, &optRegex](const char *file) {
        std::ifstream fileStream(file);
        std::string fileString((std::istreambuf_iterator<char>(fileStream)),
                               std::istreambuf_iterator<char>());
        for (std::sregex_iterator
                 i = std::sregex_iterator(fileString.begin(), fileString.end(),
                                          optRegex),
                 e = std::sregex_iterator();
             i != e; ++i) {
            std::smatch match = *i;
            string optionName = match[1];
            string optionVal = match[2];
            args.push_back(optionName);
            if (!optionVal.empty()) {
                args.push_back(optionVal);
            }
        }
    });
    return args;
}

MonoPair<SharedSMTRef> searchCustomRelations(MonoPair<std::string> fileNames,
                                             bool &additionalIn) {
    SharedSMTRef in = nullptr;
    SharedSMTRef out = nullptr;
    std::ifstream fileStream1(fileNames.first);
    std::string fileString1((std::istreambuf_iterator<char>(fileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream fileStream2(fileNames.second);
    std::string fileString2((std::istreambuf_iterator<char>(fileStream2)),
                            std::istreambuf_iterator<char>());

    searchCustomRelationsInFile(fileString1, in, out, additionalIn);
    searchCustomRelationsInFile(fileString2, in, out, additionalIn);

    return makeMonoPair(in, out);
}

void searchCustomRelationsInFile(std::string file, SharedSMTRef &in,
                                 SharedSMTRef &out, bool &additionalIn) {
    std::regex relinRegex(
        "/\\*@\\s*rel_in\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::regex reloutRegex(
        "/\\*@\\s*rel_out\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    std::regex preRegex("/\\*@\\s*pre\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
                        std::regex::ECMAScript);
    std::smatch match;
    if (in == nullptr) {
        if (std::regex_search(file, match, preRegex)) {
            std::string matchStr = match[2];
            in = stringExpr("(" + matchStr + ")");
            additionalIn = true;
        } else if (std::regex_search(file, match, relinRegex)) {
            std::string matchStr = match[2];
            std::string combinedString = "(" + matchStr + ")";
            setSMTLexerInput(combinedString.c_str());
            in = parseSMT();
        }
    }
    if (std::regex_search(file, match, reloutRegex) && out == nullptr) {
        std::string matchStr = match[2];
        out = stringExpr("(" + matchStr + ")");
    }
}

std::multimap<string, string>
searchFunctionConditions(MonoPair<string> fileNames) {
    std::multimap<string, string> map;
    std::ifstream fileStream1(fileNames.first);
    std::string fileString1((std::istreambuf_iterator<char>(fileStream1)),
                            std::istreambuf_iterator<char>());
    std::ifstream fileStream2(fileNames.second);
    std::string fileString2((std::istreambuf_iterator<char>(fileStream2)),
                            std::istreambuf_iterator<char>());
    auto map1 = searchFunctionConditionsInFile(fileString1);
    auto map2 = searchFunctionConditionsInFile(fileString2);
    std::merge(map1.begin(), map1.end(), map2.begin(), map2.end(),
               std::inserter(map, std::end(map)));
    return map;
}

std::multimap<string, string> searchFunctionConditionsInFile(std::string file) {
    std::multimap<string, string> map;
    std::regex condRegex(
        "/\\*@\\s*addfuncond\\s*(\\w*)\\s*\\(([\\s\\S]*?)\\)\\s*@\\*/",
        std::regex::ECMAScript);
    for (std::sregex_iterator
             i = std::sregex_iterator(file.begin(), file.end(), condRegex),
             e = std::sregex_iterator();
         i != e; ++i) {
        std::smatch match = *i;
        std::string matchStr = match[2];
        map.insert(make_pair(match[1], "(" + matchStr + ")"));
    }
    return map;
}

FileOptions getFileOptions(MonoPair<string> fileNames) {
    std::multimap<string, string> funConds =
        searchFunctionConditions(fileNames);
    bool additionalIn = false;
    auto relationPair = searchCustomRelations(fileNames, additionalIn);
    return FileOptions(funConds, relationPair.first, relationPair.second,
                       additionalIn);
}

set<MonoPair<string>>
parseFunctionPairFlags(llreve::cl::list<string> &functionPairFlags) {
    set<MonoPair<string>> functionPairs;
    for (const auto &flag : functionPairFlags) {
        const auto &splitted = split(flag, ',');
        if (splitted.size() != 2) {
            logError("Could not parse '" + flag + "' as a function pair\n");
            exit(1);
        }
        functionPairs.insert({splitted.at(0), splitted.at(1)});
    }
    return functionPairs;
}

set<MonoPair<llvm::Function *>>
getCoupledFunctions(MonoPair<llvm::Module &> modules, bool disableAutoCoupling,
                    std::set<MonoPair<std::string>> coupledFunctionNames) {
    if (disableAutoCoupling) {
        return lookupFunctionNamePairs(modules, coupledFunctionNames);
    } else {
        return inferCoupledFunctionsByName(modules);
    }
}
set<MonoPair<llvm::Function *>>
inferCoupledFunctionsByName(MonoPair<llvm::Module &> modules) {
    set<MonoPair<llvm::Function *>> coupledFunctions;
    for (auto &fun1 : modules.first) {
        // These functions are removed before we ever look for couplings
        if (isLlreveIntrinsic(fun1) || fun1.isIntrinsic()) {
            continue;
        }
        llvm::Function *fun2 = modules.second.getFunction(fun1.getName());
        if (!fun2) {
            continue;
        }
        coupledFunctions.insert({&fun1, fun2});
    }
    return coupledFunctions;
}

set<MonoPair<llvm::Function *>>
lookupFunctionNamePairs(MonoPair<llvm::Module &> modules,
                        std::set<MonoPair<std::string>> coupledFunctionNames) {
    set<MonoPair<llvm::Function *>> coupledFunctions;
    for (const auto namePair : coupledFunctionNames) {
        llvm::Function *fun1 = modules.first.getFunction(namePair.first);
        llvm::Function *fun2 = modules.second.getFunction(namePair.second);
        if (fun1 == nullptr) {
            logError("Could not find function '" + namePair.first +
                     "' in first module\n");
            exit(1);
        }
        if (fun2 == nullptr) {
            logError("Could not find function '" + namePair.second +
                     "' in second module\n");
            exit(1);
        }
        coupledFunctions.insert({fun1, fun2});
    }
    return coupledFunctions;
}

std::string inferMainFunctionName(const llvm::Module &module) {
    for (const auto &f : module) {
        if (!isLlreveIntrinsic(f) && !f.isIntrinsic() && !f.isDeclaration()) {
            return f.getName();
        }
    }
    logError("Could not infer a main function to analyze\n");
    exit(1);
}
MonoPair<llvm::Function *> findMainFunction(MonoPair<llvm::Module &> modules,
                                            std::string functionName) {
    if (functionName.empty()) {
        return findMainFunction(modules, inferMainFunctionName(modules.first));
    }
    auto fun1 = modules.first.getFunction(functionName);
    auto fun2 = modules.second.getFunction(functionName);
    if (fun1 == nullptr) {
        logError("Could not find function '" + functionName +
                 "' in first module\n");
        exit(1);
    }
    if (fun2 == nullptr) {
        logError("Could not find function '" + functionName +
                 "' in second module\n");
        exit(1);
    }
    return {fun1, fun2};
}

set<MonoPair<const llvm::Function *>>
addConstToFunctionPairSet(set<MonoPair<llvm::Function *>> functionPairs) {
    set<MonoPair<const llvm::Function *>> constFunctionPairs;
    for (const auto &funPair : functionPairs) {
        constFunctionPairs.insert(funPair);
    }
    return constFunctionPairs;
}

bool isLlreveIntrinsic(const llvm::Function &f) {
    return f.getName() == "__mark" || f.getName() == "__splitmark" ||
           f.getName() == "__criterion";
}
bool hasMutualFixedAbstraction(MonoPair<const llvm::Function *> functions) {
    if (functions.first->isDeclaration() || functions.second->isDeclaration()) {
        return true;
    }
    if (SMTGenerationOpts::getInstance().AssumeEquivalent.find(functions) !=
        SMTGenerationOpts::getInstance().AssumeEquivalent.end()) {
        return true;
    }
    return false;
}

bool hasFixedAbstraction(const llvm::Function &function) {
    return function.isDeclaration();
}

std::pair<map<const llvm::Function *, int>,
          MonoPair<map<int, const llvm::Function *>>>
generateFunctionMap(MonoPair<const llvm::Module &> modules) {
    map<const llvm::Function *, int> functionNumerals;
    MonoPair<map<int, const llvm::Function *>> reversedNumerals = {{}, {}};
    unsigned i = 0;
    for (const auto &function : modules.first) {
        functionNumerals.insert({&function, i});
        reversedNumerals.first.insert({i, &function});
        ++i;
    }
    i = 0;
    for (const auto &function : modules.second) {
        functionNumerals.insert({&function, i});
        reversedNumerals.second.insert({i, &function});
        ++i;
    }
    return {functionNumerals, reversedNumerals};
}
}
}
