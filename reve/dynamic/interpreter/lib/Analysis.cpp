#include "Analysis.h"

#include "CommonPattern.h"
#include "Compat.h"
#include "Interpreter.h"
#include "Linear.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Pattern.h"

#include <fstream>
#include <iostream>
#include <regex>

// I don't care about windows
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

using smt::FunDef;
using smt::SharedSMTRef;
using smt::Op;
using smt::makeBinOp;
using smt::SortedVar;

using namespace std::placeholders;

using pattern::Placeholder;
using pattern::Variable;
using pattern::InstantiatedValue;

map<int, SharedSMTRef>
analyse(string outputDirectory,
        vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
        string mainFunctionName) {
    DIR *dir = opendir(outputDirectory.c_str());
    if (dir == nullptr) {
        std::cerr << "Couldn't open directory: " << outputDirectory << "\n";
        exit(1);
    }

    // Error handling? who needs that anyway
    MonoPair<PreprocessedFunction> mainFunctionPair =
        findFunction(preprocessedFuns, mainFunctionName).getValue();

    // Get analysis results
    const MonoPair<BidirBlockMarkMap> markMaps =
        mainFunctionPair.map<BidirBlockMarkMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<MarkAnalysis>(*pair.fun);
        });
    const MonoPair<PathMap> pathMaps =
        mainFunctionPair.map<PathMap>([](PreprocessedFunction pair) {
            return pair.fam->getResult<PathAnalysis>(*pair.fun);
        });
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*mainFunctionPair.first.fun, *mainFunctionPair.second.fun);
    // TODO this should use concat
    const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) -> vector<string> {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });
    FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
    const FreeVarsMap originalFreeVarsMap = freeVarsMap;
    MonoPair<BlockNameMap> nameMap = markMaps.map<BlockNameMap>(blockNameMap);

    PatternCandidatesMap equalityCandidates;
    PatternCandidatesMap patternCandidates;
    PatternCandidatesMap constantPatterns;
    EquationsMap equationsMap;

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
            logError("Couldn't read one of the files: " + fileName1 + "\n");
            return {};
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

        // Debug output
        // analyzeExecution(makeMonoPair(c1, c2), nameMap, debugAnalysis);

        // We search for equalities first, because that way we can limit the
        // number of other patterns we need to instantiate
        findEqualities(makeMonoPair(c1, c2), nameMap, freeVarsMap,
                       equalityCandidates);
        freeVarsMap = removeEqualities(freeVarsMap, equalityCandidates);

        basicPatternCandidates(makeMonoPair(c1, c2), nameMap, freeVarsMap,
                               patternCandidates);
        analyzeExecution(
            makeMonoPair(c1, c2), nameMap,
            std::bind(instantiatePattern, std::ref(constantPatterns),
                      std::cref(freeVarsMap),
                      std::cref(*commonpattern::constantAdditionPat), _1));
        analyzeExecution(makeMonoPair(c1, c2), nameMap,
                         std::bind(populateEquationsMap, std::ref(equationsMap),
                                   std::cref(originalFreeVarsMap), _1));
    }

    std::cerr << "A = B\n";
    dumpPatternCandidates(equalityCandidates, *commonpattern::eqPat);
    std::cerr << "A + B = C\n";
    dumpPatternCandidates(patternCandidates, *commonpattern::additionPat);
    std::cerr << "A + b = C\n";
    dumpPatternCandidates(constantPatterns,
                          *commonpattern::constantAdditionPat);
    std::cerr << "Equations\n";
    dumpEquationsMap(equationsMap, originalFreeVarsMap);
    closedir(dir);
    return makeInvariantDefinitions(findSolutions(equationsMap),
                                    originalFreeVarsMap);
}

void basicPatternCandidates(MonoPair<Call<string>> calls,
                            MonoPair<BlockNameMap> nameMap,
                            FreeVarsMap freeVarsMap,
                            PatternCandidatesMap &candidates) {
    analyzeExecution(calls, nameMap,
                     std::bind(instantiatePattern, std::ref(candidates),
                               std::cref(freeVarsMap),
                               std::cref(*commonpattern::additionPat), _1));
}

void populateEquationsMap(EquationsMap &equationsMap, FreeVarsMap freeVarsMap,
                          MatchInfo match) {
    VarMap<std::string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    std::vector<mpq_class> equation(freeVarsMap.at(match.mark).size() + 1);
    for (size_t i = 0; i < equation.size() - 1; ++i) {
        string name = freeVarsMap.at(match.mark).at(i);
        equation.at(i) = variables.at(name)->unsafeIntVal();
    }
    // Add a constant at the end of each vector
    equation.at(equation.size() - 1) = 1;
    if (isZero(equation)) {
        return;
    }
    if (equationsMap.find(match.mark) == equationsMap.end()) {
        equationsMap[match.mark] = {equation};
    } else {
        vector<vector<mpq_class>> vecs = equationsMap.at(match.mark);
        vecs.push_back(equation);
        if (!linearlyIndependent(vecs)) {
            return;
        }
        equationsMap.at(match.mark).push_back(equation);
    }
}

FreeVarsMap removeEqualities(FreeVarsMap freeVars,
                             const PatternCandidatesMap &candidates) {
    for (auto mapIt : candidates) {
        list<string> vars;
        vars.insert(vars.begin(), freeVars.at(mapIt.first).begin(),
                    freeVars.at(mapIt.first).end());
        for (auto vec : mapIt.second) {
            assert(vec.size() == 2);
            assert(vec.at(0)->getType() == Placeholder::Variable);
            assert(vec.at(1)->getType() == Placeholder::Variable);
            string varName1 = static_pointer_cast<Variable>(vec.at(0))->name;
            string varName2 = static_pointer_cast<Variable>(vec.at(1))->name;
            // Sorting makes sure we don't remove both sides of an equality
            if (varName1 <= varName2) {
                vars.remove(varName2);
            } else {
                vars.remove(varName1);
            }
        }
        vector<string> varsVec;
        varsVec.insert(varsVec.end(), vars.begin(), vars.end());
        freeVars[mapIt.first] = varsVec;
    }
    return freeVars;
}

void findEqualities(MonoPair<Call<string>> calls,
                    MonoPair<BlockNameMap> nameMap, FreeVarsMap freeVarsMap,
                    PatternCandidatesMap &candidates) {
    analyzeExecution(calls, nameMap,
                     std::bind(instantiatePattern, std::ref(candidates),
                               std::cref(freeVarsMap),
                               std::cref(*commonpattern::eqPat), _1));
}

BlockNameMap blockNameMap(BidirBlockMarkMap blockMap) {
    BlockNameMap ret;
    for (auto it : blockMap.BlockToMarksMap) {
        ret[it.first->getName()] = it.second;
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
    auto prevStepIt1 = *stepsIt1;
    auto prevStepIt2 = *stepsIt2;
    while (stepsIt1 != steps1.end() && stepsIt2 != steps2.end()) {
        // Advance until a mark is reached
        while (stepsIt1 != steps1.end() &&
               !normalMarkBlock(nameMaps.first, (*stepsIt1)->blockName)) {
            stepsIt1++;
        }
        while (stepsIt2 != steps2.end() &&
               !normalMarkBlock(nameMaps.second, (*stepsIt2)->blockName)) {
            stepsIt2++;
        }
        if (stepsIt1 == steps1.end() && stepsIt2 == steps2.end()) {
            break;
        }
        // Check marks
        if (!intersection(nameMaps.first.at((*stepsIt1)->blockName),
                          nameMaps.second.at((*stepsIt2)->blockName))
                 .empty()) {
            assert(intersection(nameMaps.first.at((*stepsIt1)->blockName),
                                nameMaps.second.at((*stepsIt2)->blockName))
                       .size() == 1);
            // We resolve the ambiguity in the marks by hoping that for one
            // program there is only one choice
            int mark = *intersection(nameMaps.first.at((*stepsIt1)->blockName),
                                     nameMaps.second.at((*stepsIt2)->blockName))
                            .begin();
            // Perfect synchronization
            fun(MatchInfo(makeMonoPair(**stepsIt1, **stepsIt2), LoopInfo::None,
                          mark));
            prevStepIt1 = *stepsIt1;
            prevStepIt2 = *stepsIt2;
            ++stepsIt1;
            ++stepsIt2;
        } else {
            // In the first round this is not true, but we should never fall in
            // this case in the first round
            assert(prevStepIt1 != *stepsIt1);
            assert(prevStepIt2 != *stepsIt2);

            // One side has to wait for the other to finish its loop
            LoopInfo loop = LoopInfo::Left;
            auto stepsIt = stepsIt1;
            auto prevStepIt = prevStepIt1;
            auto prevStepItOther = prevStepIt2;
            auto end = steps1.end();
            auto nameMap = nameMaps.first;
            auto otherNameMap = nameMaps.second;
            if ((*stepsIt2)->blockName == prevStepIt2->blockName) {
                loop = LoopInfo::Right;
                stepsIt = stepsIt2;
                prevStepIt = prevStepIt2;
                prevStepItOther = prevStepIt1;
                end = steps2.end();
                nameMap = nameMaps.second;
                otherNameMap = nameMaps.first;
            }
            // Keep looping one program until it moves on
            do {
                assert(intersection(nameMap.at(prevStepIt->blockName),
                                    otherNameMap.at(prevStepItOther->blockName))
                           .size() == 1);
                int mark =
                    *intersection(nameMap.at(prevStepIt->blockName),
                                  otherNameMap.at(prevStepItOther->blockName))
                         .begin();
                // Make sure the first program is always the first argument
                if (loop == LoopInfo::Left) {
                    fun(MatchInfo(makeMonoPair(**stepsIt, *prevStepItOther),
                                  loop, mark));
                } else {
                    fun(MatchInfo(makeMonoPair(*prevStepItOther, **stepsIt),
                                  loop, mark));
                }
                // Go to the next mark
                do {
                    stepsIt++;
                } while (stepsIt != end &&
                         !normalMarkBlock(nameMap, (*stepsIt)->blockName));
                // Did we return to the same mark?
            } while (stepsIt != end &&
                     (*stepsIt)->blockName == prevStepIt->blockName);
            // Getting a reference to the iterator and modifying that doesn't
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
    return it->second.count(ENTRY_MARK) == 0;
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

void instantiatePattern(PatternCandidatesMap &patternCandidates,
                        const FreeVarsMap &freeVars, const pattern::Expr &pat,
                        MatchInfo match) {
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

EquationsSolutionsMap findSolutions(const EquationsMap &equationsMap) {
    EquationsSolutionsMap map;
    for (auto eqMapIt : equationsMap) {
        Matrix<mpq_class> m = nullSpace(eqMapIt.second);
        Matrix<mpz_class> n(m.size());
        for (size_t i = 0; i < n.size(); ++i) {
            n.at(i) = ratToInt(m.at(i));
        }
        map[eqMapIt.first] = n;
    }
    return map;
}

void dumpEquationsMap(const EquationsMap &equationsMap,
                      const FreeVarsMap &freeVarsMap) {
    EquationsSolutionsMap solutions = findSolutions(equationsMap);
    for (auto eqMapIt : solutions) {
        std::cout << eqMapIt.first << ":\n";
        for (const auto &varName : freeVarsMap.at(eqMapIt.first)) {
            std::cout << varName << "\t";
        }
        std::cout << "constant\n";
        dumpMatrix(eqMapIt.second);
    }
}

SharedSMTRef makeEquation(const vector<mpz_class> &eq,
                          const vector<string> &freeVars) {
    vector<SharedSMTRef> left;
    vector<SharedSMTRef> right;
    assert(eq.size() == freeVars.size() + 1);
    for (size_t i = 0; i < freeVars.size(); ++i) {
        if (eq.at(i) > 0) {
            if (eq.at(i) == 1) {
                left.push_back(smt::stringExpr(freeVars.at(i)));
            } else {
                left.push_back(
                    makeBinOp("*", eq.at(i).get_str(), freeVars.at(i)));
            }
        } else if (eq.at(i) < 0) {
            mpz_class inv = -eq.at(i);
            if (inv == 1) {
                right.push_back(smt::stringExpr(freeVars.at(i)));
            } else {
                right.push_back(makeBinOp("*", inv.get_str(), freeVars.at(i)));
            }
        }
    }
    if (eq.back() > 0) {
        left.push_back(smt::stringExpr(eq.back().get_str()));
    } else if (eq.back() < 0) {
        mpz_class inv = -eq.back();
        right.push_back(smt::stringExpr(inv.get_str()));
    }
    SharedSMTRef leftSide = nullptr;
    if (left.size() == 0) {
        leftSide = smt::stringExpr("0");
    } else if (left.size() == 1) {
        leftSide = left.front();
    } else {
        leftSide = make_shared<Op>("+", left);
    }
    SharedSMTRef rightSide = nullptr;
    if (right.size() == 0) {
        rightSide = smt::stringExpr("0");
    } else if (right.size() == 1) {
        rightSide = right.front();
    } else {
        rightSide = make_shared<Op>("+", right);
    }
    return makeBinOp("=", leftSide, rightSide);
}

SharedSMTRef makeInvariantDefinition(const vector<vector<mpz_class>> &solution,
                                     const vector<string> &freeVars) {
    vector<SharedSMTRef> conjunction;
    for (const auto &vec : solution) {
        conjunction.push_back(makeEquation(vec, freeVars));
    }
    return make_shared<Op>("and", conjunction);
}

map<int, SharedSMTRef>
makeInvariantDefinitions(const EquationsSolutionsMap &solutions,
                         const FreeVarsMap &freeVarsMap) {
    map<int, SharedSMTRef> definitions;
    for (auto mapIt : solutions) {
        vector<SortedVar> args;
        for (auto &var : freeVarsMap.at(mapIt.first)) {
            args.push_back(SortedVar(var, "Int"));
        }
        definitions[mapIt.first] = make_shared<FunDef>(
            "INV_MAIN_" + std::to_string(mapIt.first), args, "Bool",
            makeInvariantDefinition(mapIt.second, freeVarsMap.at(mapIt.first)));
    }
    return definitions;
}
