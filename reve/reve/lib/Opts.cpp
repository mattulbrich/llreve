#include "Opts.h"

#include "llvm/Support/CommandLine.h"

#include <fstream>
#include <regex>

using std::map;
using std::string;
using std::vector;
using smt::stringExpr;
using smt::SharedSMTRef;

llvm::cl::OptionCategory ReveCategory("Reve options",
                                      "Options for controlling reve.");

void SMTGenerationOpts::initialize(std::string mainFunction, bool heap,
                                   bool stack, bool globalConstants,
                                   bool onlyRecursive, bool noByteHeap,
                                   bool everythingSigned, bool singleInvariant,
                                   bool muZ, bool perfectSync, bool nest,
                                   bool passInputThrough,
                                   map<int, SharedSMTRef> invariants) {
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
    i.Invariants = invariants;
}

void parseCommandLineArguments(int argc, const char **argv) {
    llvm::cl::HideUnrelatedOptions(ReveCategory);
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
        llvm::cl::ParseCommandLineOptions(argc, argv, "reve\n");
    } else {
        llvm::cl::ParseCommandLineOptions(argc, argv, "reve\n");
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
            in = stringExpr("(" + matchStr + ")");
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
    bool additionalIn;
    auto relationPair = searchCustomRelations(fileNames, additionalIn);
    return FileOptions(funConds, relationPair.first, relationPair.second,
                       additionalIn);
}
