#include "Analysis.h"

#include "CommonPattern.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Pattern.h"

#include <fstream>
#include <iostream>
#include <regex>

// I don’t care about windows
#include "dirent.h"

using llvm::Module;
using llvm::Optional;

using std::make_shared;
using std::shared_ptr;
using std::string;
using std::vector;
using std::list;
using std::ifstream;
using std::ios;
using std::map;
using std::set;
using std::static_pointer_cast;

using namespace std::placeholders;

using pattern::Placeholder;
using pattern::Variable;
using pattern::InstantiatedValue;

void analyse(MonoPair<shared_ptr<llvm::Module>> modules, string outputDirectory,
             vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
             string mainFunctionName) {
    DIR *dir = opendir(outputDirectory.c_str());
    if (dir == nullptr) {
        std::cerr << "Couldn’t open directory: " << outputDirectory << "\n";
        exit(1);
    }
    // Error handling? who needs that anyway …
    MonoPair<PreprocessedFunction> mainFunctionPair =
        findFunction(preprocessedFuns, mainFunctionName).getValue();
    struct dirent *dirEntry;
    std::regex firstFileRegex("^(.*_)1(_\\d+.cbor)$", std::regex::ECMAScript);
    while ((dirEntry = readdir(dir))) {
        string fileName1 = outputDirectory + "/" + dirEntry->d_name;
        std::smatch sm;
        if (!std::regex_match(fileName1, sm, firstFileRegex)) {
            continue;
        }
        std::string fileName2 = sm[1].str() + "2" + sm[2].str();
        ifstream file1(fileName1, ios::binary | ios::ate);
        ifstream file2(fileName2, ios::binary | ios::ate);
        std::streamsize size1 = file1.tellg();
        std::streamsize size2 = file2.tellg();
        file1.seekg(0, ios::beg);
        file2.seekg(0, ios::beg);
        std::cout << fileName1 << "\n";
        std::cout << fileName2 << "\n";

        std::vector<char> buffer1(static_cast<size_t>(size1));
        std::vector<char> buffer2(static_cast<size_t>(size2));
        if (!file1.read(buffer1.data(), size1) ||
            !file2.read(buffer2.data(), size2)) {
            logError("Couldn’t read one of the files: " + fileName1 + "\n");
            return;
        }

        // deserialize
        struct cbor_load_result res;
        cbor_item_t *root =
            cbor_load(reinterpret_cast<unsigned char *>(buffer1.data()),
                      static_cast<size_t>(size1), &res);
        Call<std::string> c1 = cborToCall(root);
        cbor_decref(&root);
        root = cbor_load(reinterpret_cast<unsigned char *>(buffer2.data()),
                         static_cast<size_t>(size2), &res);
        Call<std::string> c2 = cborToCall(root);
        cbor_decref(&root);

        // Get analysis results
        const MonoPair<BidirBlockMarkMap> markMaps =
            mainFunctionPair.map<BidirBlockMarkMap>(
                [](PreprocessedFunction pair) {
                    return pair.fam->getResult<MarkAnalysis>(*pair.fun);
                });
        const MonoPair<PathMap> pathMaps =
            mainFunctionPair.map<PathMap>([](PreprocessedFunction pair) {
                return pair.fam->getResult<PathAnalysis>(*pair.fun);
            });
        const MonoPair<vector<string>> funArgsPair = functionArgs(
            *mainFunctionPair.first.fun, *mainFunctionPair.second.fun);
        // TODO this should use concat
        const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
            {},
            [](vector<string> acc, vector<string> args) -> vector<string> {
                acc.insert(acc.end(), args.begin(), args.end());
                return acc;
            });
        FreeVarsMap freeVarsMap =
            freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
        MonoPair<BlockNameMap> nameMap =
            markMaps.map<BlockNameMap>(blockNameMap);

        // Debug output
        analyzeExecution(makeMonoPair(c1, c2), nameMap, debugAnalysis);

        // We search for equalities first, because that way we can limit the
        // number of other patterns we need to instantiate
        PatternCandidatesMap equalityCandidates =
            findEqualities(makeMonoPair(c1, c2), nameMap, freeVarsMap);
        dumpPatternCandidates(equalityCandidates, *commonpattern::eqPat);
        std::cerr << "A = B\n";
        freeVarsMap = removeEqualities(freeVarsMap, equalityCandidates);

        // Other patterns, for now only a + b = c
        PatternCandidatesMap patternCandidates =
            instantiatePattern(freeVarsMap, *commonpattern::additionPat);
        basicPatternCandidates(makeMonoPair(c1, c2), nameMap,
                               patternCandidates);
        std::cerr << "A + B = C\n";
        dumpPatternCandidates(patternCandidates, *commonpattern::additionPat);

        PatternCandidatesMap constantPatterns;
        analyzeExecution(
            makeMonoPair(c1, c2), nameMap,
            std::bind(instantiatePatternWithConstant,
                      std::ref(constantPatterns), std::cref(freeVarsMap),
                      std::cref(*commonpattern::constantAdditionPat), _1));
        std::cerr << "A + b = C\n";
        dumpPatternCandidates(constantPatterns,
                              *commonpattern::constantAdditionPat);

        // Only analyze one file for now
        break;
    }

    closedir(dir);
}

void basicPatternCandidates(MonoPair<Call<string>> calls,
                            MonoPair<BlockNameMap> nameMap,
                            PatternCandidatesMap &candidates) {
    analyzeExecution(calls, nameMap,
                     std::bind(removeNonMatchingPatterns, std::ref(candidates),
                               std::cref(*commonpattern::additionPat), _1));
}

FreeVarsMap removeEqualities(FreeVarsMap freeVars,
                             const PatternCandidatesMap &candidates) {
    for (auto mapIt : candidates) {
        list<string> vars;
        vars.insert(vars.begin(), freeVars.at(mapIt.first).begin(),
                    freeVars.at(mapIt.first).end());
        for (auto vec : mapIt.second) {
            assert(vec.size() == 2);
            // Equalities are sorted lexicographically so it’s safe to throw out
            // all right sides
            assert(vec.at(1)->getType() == Placeholder::Variable);
            vars.remove(static_pointer_cast<Variable>(vec.at(1))->name);
        }
        vector<string> varsVec;
        varsVec.insert(varsVec.end(), vars.begin(), vars.end());
        freeVars[mapIt.first] = varsVec;
    }
    return freeVars;
}

PatternCandidatesMap findEqualities(MonoPair<Call<string>> calls,
                                    MonoPair<BlockNameMap> nameMap,
                                    FreeVarsMap freeVars) {
    PatternCandidatesMap maps;
    for (auto it : freeVars) {
        for (size_t i = 0; i < it.second.size(); ++i) {
            for (size_t j = i + 1; j < it.second.size(); ++j) {
                auto var1 = it.second[i];
                auto var2 = it.second[j];
                if (var1 <= var2) {
                    maps[it.first].push_back({make_shared<Variable>(var1),
                                              make_shared<Variable>(var2)});
                } else {
                    maps[it.first].push_back({make_shared<Variable>(var2),
                                              make_shared<Variable>(var1)});
                }
            }
        }
    }

    analyzeExecution(calls, nameMap,
                     std::bind(removeNonMatchingPatterns, std::ref(maps),
                               std::cref(*commonpattern::eqPat), _1));
    return maps;
}

map<string, int> blockNameMap(BidirBlockMarkMap blockMap) {
    map<string, int> ret;
    for (auto it : blockMap.BlockToMarksMap) {
        assert(it.second.size() == 1);
        ret[it.first->getName()] = *it.second.begin();
    }
    return ret;
}

Optional<MonoPair<PreprocessedFunction>>
findFunction(const vector<MonoPair<PreprocessedFunction>> functions,
             string functionName) {
    for (auto &f : functions) {
        if (f.first.fun->getName() == functionName) {
            return Optional<MonoPair<PreprocessedFunction>>(f);
        }
    }
    return Optional<MonoPair<PreprocessedFunction>>();
}

void analyzeExecution(MonoPair<Call<std::string>> calls,
                      MonoPair<BlockNameMap> nameMaps,
                      std::function<void(MatchInfo)> fun) {
    auto steps1 = calls.first.steps;
    auto steps2 = calls.second.steps;
    auto stepsIt1 = steps1.begin();
    auto stepsIt2 = steps2.begin();
    while (stepsIt1 != steps1.end() && stepsIt2 != steps2.end()) {
        // Advance until a mark is reached
        auto prevStepIt1 = *stepsIt1;
        while (!normalMarkBlock(nameMaps.first, (*stepsIt1)->blockName) &&
               stepsIt1 != steps1.end()) {
            stepsIt1++;
        }
        auto prevStepIt2 = *stepsIt2;
        while (!normalMarkBlock(nameMaps.second, (*stepsIt2)->blockName) &&
               stepsIt2 != steps2.end()) {
            stepsIt2++;
        }
        // Check marks
        if (nameMaps.first.at((*stepsIt1)->blockName) ==
            nameMaps.second.at((*stepsIt2)->blockName)) {
            // Perfect synchronization
            fun(MatchInfo(makeMonoPair(**stepsIt1, **stepsIt2), LoopInfo::None,
                          nameMaps.first.at((*stepsIt1)->blockName)));
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // One side has to wait for the other to finish its loop
            LoopInfo loop = LoopInfo::Left;
            auto &stepsIt = stepsIt1;
            auto prevStepIt = prevStepIt1;
            auto prevStepItOther = prevStepIt2;
            auto end = steps1.end();
            // Only a reference for performance reasons
            auto &nameMap = nameMaps.first;
            if ((*stepsIt2)->blockName == prevStepIt2->blockName) {
                loop = LoopInfo::Right;
                stepsIt = stepsIt2;
                prevStepIt = prevStepIt2;
                prevStepItOther = prevStepIt1;
                end = steps2.end();
                nameMap = nameMaps.second;
            }
            // Keep looping one program until it moves on
            do {
                fun(MatchInfo(makeMonoPair(**stepsIt, *prevStepItOther), loop,
                              nameMap.at(prevStepIt->blockName)));
                // Go to the next mark
                do {
                    stepsIt++;
                } while (stepsIt != end &&
                         !normalMarkBlock(nameMap, (*stepsIt)->blockName));
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     (*stepsIt)->blockName == prevStepIt->blockName);
            // Getting a reference to the iterator and modifying that doesn’t
            // seem to work so we copy it and set it again
            if (loop == LoopInfo::Left) {
                stepsIt1 = stepsIt;
            } else {
                stepsIt2 = stepsIt;
            }
        }
    }
}

bool normalMarkBlock(const BlockNameMap &map, BlockName &blockName) {
    auto it = map.find(blockName);
    if (it == map.end()) {
        return false;
    }
    return it->second != ENTRY_MARK;
}

void debugAnalysis(MatchInfo match) {
    switch (match.loopInfo) {
    case LoopInfo::None:
        std::cout << "Perfect sync";
        break;
    case LoopInfo::Left:
        std::cout << "Left program is looping";
        break;
    case LoopInfo::Right:
        std::cout << "Right program is looping";
        break;
    }
    std::cout << std::endl;
    std::cout << "First state:" << std::endl;
    std::cout << match.steps.first.toJSON(identity<string>).dump(4)
              << std::endl;
    std::cout << "Second state:" << std::endl;
    std::cout << match.steps.second.toJSON(identity<string>).dump(4)
              << std::endl;
    std::cout << std::endl << std::endl;
}

void instantiatePatternWithConstant(PatternCandidatesMap &patternCandidates,
                                    const FreeVarsMap &freeVars,
                                    const pattern::Expr &pat, MatchInfo match) {
    VarMap<string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    if (patternCandidates.find(match.mark) == patternCandidates.end()) {
        // Instantiate the first time
        patternCandidates[match.mark] =
            pat.instantiate(freeVars.at(match.mark), variables);
    } else {
        // Already instantiated, remove the non matching instantiations
        auto &list = patternCandidates.at(match.mark);
        vector<VarIntVal> candidateVals(pat.arguments());
        for (auto listIt = list.begin(), e = list.end(); listIt != e;) {
            for (size_t i = 0; i < candidateVals.size(); ++i) {
                candidateVals.at(i) = listIt->at(i)->getValue(variables);
            }
            if (!pat.matches(candidateVals)) {
                listIt = list.erase(listIt);
            } else {
                ++listIt;
            }
        }
    }
}

void removeNonMatchingPatterns(PatternCandidatesMap &patternCandidates,
                               const pattern::Expr &pat, MatchInfo match) {
    VarMap<string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    vector<VarIntVal> candidateVals(pat.arguments());
    auto &list = patternCandidates[match.mark];
    for (auto listIt = list.begin(), e = list.end(); listIt != e;) {
        for (size_t i = 0; i < candidateVals.size(); ++i) {
            candidateVals.at(i) = listIt->at(i)->getValue(variables);
        }
        if (!pat.matches(candidateVals)) {
            listIt = list.erase(listIt);
        } else {
            ++listIt;
        }
    }
}

void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat) {
    for (auto it : candidates) {
        std::cout << it.first << ":\n";
        for (auto vec : it.second) {
            std::cout << "\t";
            pat.dump(std::cout, vec);
            std::cout << std::endl;
        }
    }
}

PatternCandidatesMap instantiatePattern(map<int, vector<string>> variables,
                                        const pattern::Expr &pat) {
    map<int, list<vector<shared_ptr<InstantiatedValue>>>> output;
    for (auto mapIt : variables) {
        vector<shared_ptr<InstantiatedValue>> args;
        for (auto arg : mapIt.second) {
            args.push_back(make_shared<Variable>(arg));
        }
        if (pat.arguments() <= mapIt.second.size()) {
            output.insert(std::make_pair(mapIt.first,
                                         kPermutations(args, pat.arguments())));
        } else {
            std::list<std::vector<shared_ptr<InstantiatedValue>>> l;
            output.insert(std::make_pair(mapIt.first, l));
        }
    }
    return output;
}
