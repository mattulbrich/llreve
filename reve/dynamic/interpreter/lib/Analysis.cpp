#include "Analysis.h"

#include "FunctionSMTGeneration.h"
#include "Interpreter.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"

#include <fstream>
#include <iostream>
#include <regex>

// I don’t care about windows
#include "dirent.h"

using llvm::Module;
using llvm::Optional;

using std::shared_ptr;
using std::string;
using std::vector;
using std::ifstream;
using std::ios;
using std::map;
using std::set;
using namespace std::placeholders;

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
        // std::cout << "buffersize: " << size << "\n";
        std::cout << fileName1 << "\n";
        std::cout << fileName2 << "\n";

        std::vector<char> buffer1(static_cast<size_t>(size1));
        std::vector<char> buffer2(static_cast<size_t>(size2));
        if (!file1.read(buffer1.data(), size1) ||
            !file2.read(buffer2.data(), size2)) {
            logError("Couldn’t read one of the files: " + fileName1 + "\n");
            return;
        }
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
        map<int, set<Equality>> equalityMap =
            findEqualities(makeMonoPair(c1, c2), mainFunctionPair);
        for (auto it : equalityMap) {
            std::cout << it.first << ":\n";
            for (auto eq : it.second) {
                std::cout << "\t";
                std::cout << eq;
                std::cout << "\n";
            }
        }
        break;
    }
    closedir(dir);
}

map<int, set<Equality>>
findEqualities(MonoPair<Call<string>> calls,
               MonoPair<PreprocessedFunction> functions) {
    map<int, set<Equality>> maps;
    const MonoPair<BidirBlockMarkMap> markMaps =
        functions.map<BidirBlockMarkMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<MarkAnalysis>(*pair.fun);
        });
    const MonoPair<PathMap> pathMaps =
        functions.map<PathMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<PathAnalysis>(*pair.fun);
        });
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*functions.first.fun, *functions.second.fun);
    // TODO this should use concat
    const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) -> vector<string> {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });
    const FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
    for (auto it : freeVarsMap) {
        if (it.first != ENTRY_MARK && it.first != EXIT_MARK) {
            for (size_t i = 0; i < it.second.size(); ++i) {
                for (size_t j = i + 1; j < it.second.size(); ++j) {
                    auto var1 = it.second[i];
                    auto var2 = it.second[j];
                    if (var1 <= var2) {
                        maps[it.first].insert(makeMonoPair(var1, var2));
                    } else {
                        maps[it.first].insert(makeMonoPair(var2, var1));
                    }
                }
            }
        }
    }
    MonoPair<BlockNameMap> nameMap = markMaps.map<BlockNameMap>(
        [](BidirBlockMarkMap m) { return blockNameMap(m); });
    analyzeExecution(calls, markMaps.first, nameMap, debugAnalysis);
    analyzeExecution(calls, markMaps.first, nameMap,
                     std::bind(removeEqualities, std::ref(maps), _1));
    // calls.forEach([](Call<string> c) {
    //     std::cout << c.toJSON(identity<string>).dump(4) << std::endl;
    // });
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
                      BidirBlockMarkMap markMap,
                      MonoPair<BlockNameMap> nameMaps,
                      std::function<void(MatchInfo)> fun) {
    auto steps1 = calls.first.steps;
    auto steps2 = calls.second.steps;
    auto stepsIt1 = steps1.begin();
    auto stepsIt2 = steps2.begin();
    while (stepsIt1 != steps1.end() && stepsIt2 != steps2.end()) {
        // assert(nameMap.at((*stepsIt1)->blockName) ==
        //        nameMap.at((*stepsIt2)->blockName));
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
            while ((*stepsIt)->blockName == prevStepIt->blockName) {
                fun(MatchInfo(makeMonoPair(**stepsIt, *prevStepItOther), loop,
                              nameMap.at(prevStepIt->blockName)));
                // Go to tnext mark
                while (!normalMarkBlock(nameMap, (*stepsIt)->blockName) &&
                       stepsIt != end) {
                    stepsIt++;
                }
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

void removeEqualities(map<int, set<Equality>> &equalities, MatchInfo match) {
    if (match.mark == EXIT_MARK) {
        return;
    }
    VarMap<string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    for (auto it1 : variables) {
        for (auto it2 : variables) {
            if (!varValEq(*it1.second, *it2.second)) {
                equalities.at(match.mark)
                    .erase(makeMonoPair(it1.first, it2.first));
                equalities.at(match.mark)
                    .erase(makeMonoPair(it2.first, it1.first));
            }
        }
    }
}
