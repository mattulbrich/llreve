#include "Analysis.h"

#include "CommonPattern.h"
#include "Compat.h"
#include "Interpreter.h"
#include "Linear.h"
#include "MarkAnalysis.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Pattern.h"
#include "SerializeTraces.h"
#include "Unroll.h"

#include <fstream>
#include <iostream>
#include <regex>

// I don't care about windows
#include <dirent.h>
#include <sys/stat.h>

#include "ModuleSMTGeneration.h"

#include "llvm/IR/Verifier.h"

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
using std::multiset;

using smt::FunDef;
using smt::SharedSMTRef;
using smt::Op;
using smt::makeBinOp;
using smt::SortedVar;

using namespace std::placeholders;

using pattern::Placeholder;
using pattern::Variable;
using pattern::InstantiatedValue;

static llvm::cl::opt<bool>
    MultinomialsFlag("multinomials", llvm::cl::desc("Use true multinomials"));
static llvm::cl::opt<unsigned>
    DegreeFlag("degree", llvm::cl::desc("Degree of the polynomial invariants"),
               llvm::cl::init(1));
static llvm::cl::opt<bool> ImplicationsFlag(
    "implications",
    llvm::cl::desc("Add implications instead of replacing invariants"));

void iterateDeserialized(
    string directory, std::function<void(MonoPair<Call<string>> &)> callback) {
    DIR *dir = opendir(directory.c_str());
    if (dir == nullptr) {
        logError("Couldn't open directory: " + directory + "\n");
    }
    struct dirent *dirEntry;
    std::regex firstFileRegex("^(.*_)1(_\\d+.cbor)$", std::regex::ECMAScript);
    while ((dirEntry = readdir(dir))) {
        string fileName1 = directory + "/" + dirEntry->d_name;
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

        std::vector<char> buffer1(static_cast<size_t>(size1));
        std::vector<char> buffer2(static_cast<size_t>(size2));
        if (!file1.read(buffer1.data(), size1) ||
            !file2.read(buffer2.data(), size2)) {
            logError("Couldn't read one of the files: " + fileName1 + "\n");
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
        MonoPair<Call<string>> calls = makeMonoPair(c1, c2);
        callback(calls);
    }
    closedir(dir);
}

vector<SharedSMTRef>
driver(MonoPair<std::shared_ptr<llvm::Module>> modules, string outputDirectory,
       vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
       string mainFunctionName) {
    auto preprocessedFunctions =
        findFunction(preprocessedFuns, mainFunctionName);
    if (!preprocessedFunctions) {
        logError("No function with the supplied name\n");
        return {};
    }
    auto functions = preprocessedFunctions.getValue().map<llvm::Function *>(
        [](PreprocessedFunction f) { return f.fun; });
    const MonoPair<BidirBlockMarkMap> markMaps =
        preprocessedFunctions.getValue().map<BidirBlockMarkMap>(
            [](PreprocessedFunction fun) { return fun.results.blockMarkMap; });
    MonoPair<BlockNameMap> nameMap = markMaps.map<BlockNameMap>(blockNameMap);
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*preprocessedFunctions.getValue().first.fun,
                     *preprocessedFunctions.getValue().second.fun);
    const vector<string> funArgs = funArgsPair.foldl<vector<string>>(
        {},
        [](vector<string> acc, vector<string> args) -> vector<string> {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });

    // Create the directory for the interpreter
    mkdir(outputDirectory.c_str(),
          S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IWOTH);
    if (errno == EEXIST) {
        logError("Directory already exists\n");
        return {};
    }

    // Run the interpreter the first time
    serializeValuesInRange(functions, -100, 100, outputDirectory);

    // Collect loop info
    LoopCountMap loopCounts;
    iterateDeserialized(outputDirectory, [&loopCounts, &nameMap](
                                             MonoPair<Call<string>> &calls) {
        int lastMark = -5; // -5 is unused
        analyzeExecution(calls, nameMap,
                         std::bind(findLoopCounts, std::ref(lastMark),
                                   std::ref(loopCounts), _1));
    });
    map<int, LoopTransformation> loopTransformations =
        findLoopTransformations(loopCounts);
    dumpLoopTransformations(loopTransformations);

    // Peel and unroll loops
    applyLoopTransformation(preprocessedFunctions.getValue(),
                            loopTransformations, markMaps);

    // Create the directory for interpreting the unrolled code
    string unrolledOutputDirectory = outputDirectory + "_unrolled";
    mkdir(unrolledOutputDirectory.c_str(),
          S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IWOTH);
    if (errno == EEXIST) {
        logError("Directory already exists\n");
        return {};
    }

    // Run the interpreter on the unrolled code
    serializeValuesInRange(functions, -100, 100, unrolledOutputDirectory);

    loopCounts = {};
    PolynomialEquations polynomialEquations;
    const MonoPair<PathMap> pathMaps =
        preprocessedFunctions.getValue().map<PathMap>(
            [](PreprocessedFunction fun) { return fun.results.paths; });
    FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
    size_t degree = DegreeFlag;
    iterateDeserialized(
        unrolledOutputDirectory,
        [&loopCounts, &nameMap, &polynomialEquations, &freeVarsMap,
         degree](MonoPair<Call<string>> &calls) {
            int lastMark = -5; // -5 is unused
            analyzeExecution(calls, nameMap,
                             std::bind(findLoopCounts, std::ref(lastMark),
                                       std::ref(loopCounts), _1));
            analyzeExecution(calls, nameMap,
                             std::bind(populateEquationsMap,
                                       std::ref(polynomialEquations),
                                       std::cref(freeVarsMap), _1, degree));
        });
    loopTransformations = findLoopTransformations(loopCounts);
    dumpLoopTransformations(loopTransformations);
    dumpPolynomials(polynomialEquations, freeVarsMap, DegreeFlag);

    auto invariantCandidates = makeInvariantDefinitions(
        findSolutions(polynomialEquations), {}, freeVarsMap, DegreeFlag);
    if (ImplicationsFlag) {
        SMTGenerationOpts::initialize(mainFunctionName, false, false, false,
                                      false, false, false, false, false, false,
                                      false, false, {});
    } else {
        SMTGenerationOpts::initialize(mainFunctionName, false, false, false,
                                      false, false, false, false, false, false,
                                      false, false, invariantCandidates);
    }
    llvm::verifyModule(*modules.first);
    llvm::verifyModule(*modules.second);
    // TODO pass all functions
    vector<SharedSMTRef> clauses =
        generateSMT(modules, {preprocessedFunctions.getValue()},
                    FileOptions({}, nullptr, nullptr, false));
    if (ImplicationsFlag) {
        // Add the necessary implications
        for (auto invariantIt : invariantCandidates) {
            auto mark = invariantIt.first;
            if (mark < 0) {
                continue;
            }
            vector<SortedVar> args;
            for (auto var : freeVarsMap.at(mark)) {
                args.push_back(SortedVar(var, "Int"));
            }
            string invariantName = "INV_MAIN_" + std::to_string(mark);
            string candidateName = invariantName + "_INFERRED";
            SharedSMTRef candidate =
                smt::makeOp(candidateName, freeVarsMap.at(mark));
            SharedSMTRef invariant =
                smt::makeOp(invariantName, freeVarsMap.at(mark));
            SharedSMTRef impl = makeBinOp("=>", invariant, candidate);
            SharedSMTRef forall = make_shared<smt::Forall>(args, impl);
            clauses.push_back(invariantIt.second);
            clauses.push_back(make_shared<smt::Assert>(forall));
        }
    }
    return clauses;
}

void applyLoopTransformation(
    MonoPair<PreprocessedFunction> &functions,
    const map<int, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &marks) {
    for (auto mapIt : loopTransformations) {
        switch (mapIt.second.type) {
        case LoopTransformType::Peel:
            if (mapIt.second.count == 0) {
                continue;
            }
            switch (mapIt.second.side) {
            case LoopTransformSide::Left:
                assert(mapIt.second.count == 1);
                peelAtMark(*functions.first.fun, mapIt.first, marks.first, "1");
                break;
            case LoopTransformSide::Right:
                peelAtMark(*functions.second.fun, mapIt.first, marks.second,
                           "2");
                break;
            }
            break;
        case LoopTransformType::Unroll:
            switch (mapIt.second.side) {
            case LoopTransformSide::Left:
                unrollAtMark(*functions.first.fun, mapIt.first, marks.first,
                             mapIt.second.count);
                break;
            case LoopTransformSide::Right:
                unrollAtMark(*functions.second.fun, mapIt.first, marks.second,
                             mapIt.second.count);
                break;
            }
            break;
        }
    }
    // Update path analysis
    functions.first.results.paths = findPaths(marks.first);
    functions.second.results.paths = findPaths(marks.second);
}

map<int, SharedSMTRef>
analyse(string outputDirectory,
        vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
        string mainFunctionName) {

    // Error handling? who needs that anyway
    MonoPair<PreprocessedFunction> mainFunctionPair =
        findFunction(preprocessedFuns, mainFunctionName).getValue();

    // Get analysis results
    const MonoPair<BidirBlockMarkMap> markMaps =
        mainFunctionPair.map<BidirBlockMarkMap>(
            [](PreprocessedFunction fun) { return fun.results.blockMarkMap; });
    const MonoPair<PathMap> pathMaps = mainFunctionPair.map<PathMap>(
        [](PreprocessedFunction fun) { return fun.results.paths; });
    const MonoPair<vector<string>> funArgsPair =
        functionArgs(*mainFunctionPair.first.fun, *mainFunctionPair.second.fun);
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
    PatternCandidatesMap lePatterns;
    PolynomialEquations polynomialEquations;
    BoundsMap boundsMap;
    LoopCountMap loopCounts;

    iterateDeserialized(
        outputDirectory,
        [&nameMap, &freeVarsMap, &boundsMap, &lePatterns, &originalFreeVarsMap,
         &polynomialEquations, &equalityCandidates, &patternCandidates,
         &loopCounts, &constantPatterns](MonoPair<Call<string>> &calls) {

            // Debug output
            // analyzeExecution(makeMonoPair(c1, c2), nameMap, debugAnalysis);

            findEqualities(calls, nameMap, freeVarsMap, equalityCandidates);

            basicPatternCandidates(calls, nameMap, freeVarsMap,
                                   patternCandidates);
            analyzeExecution(
                calls, nameMap,
                std::bind(instantiatePattern, std::ref(constantPatterns),
                          std::cref(freeVarsMap),
                          std::cref(*commonpattern::constantAdditionPat), _1));
            analyzeExecution(calls, nameMap,
                             std::bind(populateEquationsMap,
                                       std::ref(polynomialEquations),
                                       std::cref(originalFreeVarsMap), _1, 1));
            analyzeExecution(calls, nameMap,
                             std::bind(instantiatePattern, std::ref(lePatterns),
                                       std::cref(freeVarsMap),
                                       std::cref(*commonpattern::lePat), _1));
            map<int, map<string, Bound<VarIntVal>>> bounds;
            analyzeExecution(calls, nameMap,
                             std::bind(instantiateBounds, std::ref(bounds),
                                       std::cref(freeVarsMap), _1));
            int lastMark = -5; // -5 is unused
            analyzeExecution(calls, nameMap,
                             std::bind(findLoopCounts, std::ref(lastMark),
                                       std::ref(loopCounts), _1));
            boundsMap = updateBounds(boundsMap, bounds);
        });

    std::cerr << "----------\n";
    std::cerr << "A = B\n";
    dumpPatternCandidates(equalityCandidates, *commonpattern::eqPat);
    std::cerr << "----------\n";
    std::cerr << "A + B = C\n";
    dumpPatternCandidates(patternCandidates, *commonpattern::additionPat);
    std::cerr << "----------\n";
    std::cerr << "A + b = C\n";
    dumpPatternCandidates(constantPatterns,
                          *commonpattern::constantAdditionPat);
    std::cerr << "----------\n";
    std::cerr << "A <= B\n";
    dumpPatternCandidates(lePatterns, *commonpattern::lePat);
    dumpBounds(boundsMap);
    std::cerr << "----------\n";
    std::cerr << "Equations\n";
    dumpPolynomials(polynomialEquations, originalFreeVarsMap, 1);
    dumpLoopCounts(loopCounts);

    map<int, LoopTransformation> unrollSuggestions =
        findLoopTransformations(loopCounts);
    std::cerr << "----------\n";
    std::cerr << "Loop transformations\n";
    for (auto mapIt : unrollSuggestions) {
        std::cerr << mapIt.first << ": ";
        switch (mapIt.second.side) {
        case LoopTransformSide::Left:
            std::cerr << "Left:\t";
            break;
        case LoopTransformSide::Right:
            std::cerr << "Right:\t";
            break;
        }
        switch (mapIt.second.type) {
        case LoopTransformType::Unroll:
            std::cerr << "Unroll:\t";
            break;
        case LoopTransformType::Peel:
            std::cerr << "Peel:\t";
            break;
        }
        std::cerr << mapIt.second.count << "\n";
    }
    return {};
    // return makeInvariantDefinitions(findSolutions(polynomialEquations),
    //                                 boundsMap, originalFreeVarsMap);
}

void dumpLoopTransformations(map<int, LoopTransformation> loopTransformations) {
    std::cerr << "Loop transformations\n";
    for (auto mapIt : loopTransformations) {
        std::cerr << mapIt.first << ": ";
        switch (mapIt.second.side) {
        case LoopTransformSide::Left:
            std::cerr << "Left:\t";
            break;
        case LoopTransformSide::Right:
            std::cerr << "Right:\t";
            break;
        }
        switch (mapIt.second.type) {
        case LoopTransformType::Unroll:
            std::cerr << "Unroll:\t";
            break;
        case LoopTransformType::Peel:
            std::cerr << "Peel:\t";
            break;
        }
        std::cerr << mapIt.second.count << "\n";
    }
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

void findLoopCounts(int &lastMark, LoopCountMap &map, MatchInfo match) {
    if (lastMark == match.mark) {
        switch (match.loopInfo) {
        case LoopInfo::Left:
            map[match.mark].back().first++;
            break;
        case LoopInfo::Right:
            map[match.mark].back().second++;
            break;
        case LoopInfo::None:
            map[match.mark].back().first++;
            map[match.mark].back().second++;
            break;
        }
    } else {
        switch (match.loopInfo) {
        case LoopInfo::None:
            map[match.mark].push_back(makeMonoPair(0, 0));
            break;
        default:
            assert(false);
            break;
        }
        lastMark = match.mark;
    }
}

map<int, LoopTransformation> findLoopTransformations(LoopCountMap &map) {
    std::map<int, int64_t> peelCount;
    std::map<int, float> unrollQuotients;
    for (auto mapIt : map) {
        int mark = mapIt.first;
        for (auto sample : mapIt.second) {
            if (peelCount.count(mark) == 0) {
                peelCount.insert(
                    std::make_pair(mark, sample.first - sample.second));
            } else {
                if (abs(peelCount.at(mark)) <
                    abs(sample.first - sample.second)) {
                    peelCount.at(mark) = sample.first - sample.second;
                }
            }
            if (sample.first != 0 && sample.second != 0) {
                if (unrollQuotients.count(mark) == 0) {
                    unrollQuotients.insert(std::make_pair(
                        mark, static_cast<float>(sample.first) /
                                  static_cast<float>(sample.second)));
                } else {
                    float quotient = unrollQuotients.at(mark);
                    quotient = quotient < 1 ? 1 / quotient : quotient;
                    float newQuotient = static_cast<float>(sample.first) /
                                        static_cast<float>(sample.second);
                    newQuotient =
                        newQuotient < 1 ? 1 / newQuotient : newQuotient;
                    if (newQuotient > quotient) {
                        unrollQuotients.at(mark) =
                            static_cast<float>(sample.first) /
                            static_cast<float>(sample.second);
                    }
                }
            }
        }
    }
    std::map<int, LoopTransformation> transforms;
    for (auto it : peelCount) {
        int mark = it.first;
        if (abs(it.second) <= 4) {
            LoopTransformSide side = it.second >= 0 ? LoopTransformSide::Left
                                                    : LoopTransformSide::Right;
            // Fun fact: abs is not guaranteed to return a positive result
            transforms.insert(std::make_pair(
                mark, LoopTransformation(LoopTransformType::Peel, side,
                                         static_cast<size_t>(abs(it.second)))));
        } else if (unrollQuotients.count(mark) == 1) {
            float factor = unrollQuotients.at(mark);
            LoopTransformSide side =
                factor < 1 ? LoopTransformSide::Left : LoopTransformSide::Right;
            factor = factor < 1 ? 1 / factor : factor;
            transforms.insert(std::make_pair(
                mark,
                LoopTransformation(LoopTransformType::Unroll, side,
                                   static_cast<size_t>(std::round(factor)))));
        }
    }
    return transforms;
}

vector<vector<string>> polynomialTermsOfDegree(vector<string> variables,
                                               size_t degree) {
    if (MultinomialsFlag) {
        return kCombinationsWithRepetitions(variables, degree);
    } else {
        vector<vector<string>> terms;
        for (auto var : variables) {
            vector<string> term(degree, var);
            terms.push_back(term);
        }
        return terms;
    }
}

void populateEquationsMap(PolynomialEquations &polynomialEquations,
                          FreeVarsMap freeVarsMap, MatchInfo match,
                          size_t degree) {
    VarMap<string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    vector<mpq_class> equation;
    for (size_t i = 1; i <= degree; ++i) {
        auto polynomialTerms =
            polynomialTermsOfDegree(freeVarsMap.at(match.mark), i);
        for (auto term : polynomialTerms) {
            VarIntVal termVal = 1;
            for (auto var : term) {
                termVal *= variables.at(var)->unsafeIntVal();
            }
            equation.push_back(termVal);
        }
    }
    // Add a constant at the end of each vector
    equation.push_back(1);
    ExitIndex exitIndex = 0;
    if (variables.count("exitIndex$1_" + std::to_string(match.mark)) == 1) {
        exitIndex = variables.at("exitIndex$1_" + std::to_string(match.mark))
                        ->unsafeIntVal();
    } else if (variables.count("exitIndex$2_" + std::to_string(match.mark)) ==
               1) {
        exitIndex = variables.at("exitIndex$2_" + std::to_string(match.mark))
                        ->unsafeIntVal();
    }
    if (polynomialEquations[match.mark].count(exitIndex) == 0) {
        polynomialEquations.at(match.mark)
            .insert(
                make_pair(exitIndex,
                          LoopInfoData<vector<vector<mpq_class>>>({}, {}, {})));
        switch (match.loopInfo) {
        case LoopInfo::Left:
            polynomialEquations.at(match.mark).at(exitIndex).left = {equation};
            break;
        case LoopInfo::Right:
            polynomialEquations.at(match.mark).at(exitIndex).right = {equation};
            break;
        case LoopInfo::None:
            polynomialEquations.at(match.mark).at(exitIndex).none = {equation};
            break;
        }
    } else {
        vector<vector<mpq_class>> vecs;
        switch (match.loopInfo) {
        case LoopInfo::Left:
            vecs = polynomialEquations.at(match.mark).at(exitIndex).left;
            break;
        case LoopInfo::Right:
            vecs = polynomialEquations.at(match.mark).at(exitIndex).right;
            break;
        case LoopInfo::None:
            vecs = polynomialEquations.at(match.mark).at(exitIndex).none;
            break;
        }
        vecs.push_back(equation);
        if (!linearlyIndependent(vecs)) {
            return;
        }
        switch (match.loopInfo) {
        case LoopInfo::Left:
            polynomialEquations.at(match.mark)
                .at(exitIndex)
                .left.push_back(equation);
            break;
        case LoopInfo::Right:
            polynomialEquations.at(match.mark)
                .at(exitIndex)
                .right.push_back(equation);
            break;
        case LoopInfo::None:
            polynomialEquations.at(match.mark)
                .at(exitIndex)
                .none.push_back(equation);
            break;
        }
    }
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
        std::cerr << "Perfect sync";
        break;
    case LoopInfo::Left:
        std::cerr << "Left program is looping";
        break;
    case LoopInfo::Right:
        std::cerr << "Right program is looping";
        break;
    }
    std::cerr << std::endl;
    std::cerr << "First state:" << std::endl;
    std::cerr << match.steps.first.toJSON(identity<string>).dump(4)
              << std::endl;
    std::cerr << "Second state:" << std::endl;
    std::cerr << match.steps.second.toJSON(identity<string>).dump(4)
              << std::endl;
    std::cerr << std::endl << std::endl;
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
        patternCandidates.insert(
            make_pair(match.mark, LoopInfoData<Optional<PatternCandidates>>(
                                      Optional<PatternCandidates>(),
                                      Optional<PatternCandidates>(),
                                      Optional<PatternCandidates>())));
        switch (match.loopInfo) {
        case LoopInfo::Left:
            patternCandidates.at(match.mark).left =
                pat.instantiate(freeVars.at(match.mark), variables);
            break;
        case LoopInfo::Right:
            patternCandidates.at(match.mark).right =
                pat.instantiate(freeVars.at(match.mark), variables);
            break;
        case LoopInfo::None:
            patternCandidates.at(match.mark).none =
                pat.instantiate(freeVars.at(match.mark), variables);
            break;
        }
    } else {
        PatternCandidates *list = nullptr;
        switch (match.loopInfo) {
        case LoopInfo::Left:
            if (!patternCandidates.at(match.mark).left.hasValue()) {
                patternCandidates.at(match.mark).left =
                    pat.instantiate(freeVars.at(match.mark), variables);
                return;
            } else {
                list = &patternCandidates.at(match.mark).left.getValue();
            }
            break;
        case LoopInfo::Right:
            if (!patternCandidates.at(match.mark).right.hasValue()) {
                patternCandidates.at(match.mark).right =
                    pat.instantiate(freeVars.at(match.mark), variables);
                return;
            } else {
                list = &patternCandidates.at(match.mark).right.getValue();
            }
            break;
        case LoopInfo::None:
            if (!patternCandidates.at(match.mark).none.hasValue()) {
                patternCandidates.at(match.mark).none =
                    pat.instantiate(freeVars.at(match.mark), variables);
                return;
            } else {
                list = &patternCandidates.at(match.mark).none.getValue();
            }
            break;
        }
        // Already instantiated, remove the non matching instantiations
        vector<VarIntVal> candidateVals(pat.arguments());
        for (auto listIt = list->begin(), e = list->end(); listIt != e;) {
            for (size_t i = 0; i < candidateVals.size(); ++i) {
                candidateVals.at(i) = listIt->at(i)->getValue(variables);
            }
            if (!pat.matches(candidateVals)) {
                listIt = list->erase(listIt);
            } else {
                ++listIt;
            }
        }
    }
}

void dumpPatternCandidates(const PatternCandidatesMap &candidates,
                           const pattern::Expr &pat) {
    for (auto it : candidates) {
        std::cerr << it.first << ":\n";
        if (it.second.left.hasValue()) {
            std::cerr << "left:\n";
            for (auto vec : it.second.left.getValue()) {
                std::cerr << "\t";
                pat.dump(std::cerr, vec);
                std::cerr << std::endl;
            }
        }
        if (it.second.right.hasValue()) {
            std::cerr << "right:\n";
            for (auto vec : it.second.right.getValue()) {
                std::cerr << "\t";
                pat.dump(std::cerr, vec);
                std::cerr << std::endl;
            }
        }
        if (it.second.none.hasValue()) {
            std::cerr << "none:\n";
            for (auto vec : it.second.none.getValue()) {
                std::cerr << "\t";
                pat.dump(std::cerr, vec);
                std::cerr << std::endl;
            }
        }
    }
}

PolynomialSolutions
findSolutions(const PolynomialEquations &polynomialEquations) {
    PolynomialSolutions map;
    for (auto eqMapIt : polynomialEquations) {
        int mark = eqMapIt.first;
        for (auto exitMapIt : eqMapIt.second) {
            ExitIndex exitIndex = exitMapIt.first;
            LoopInfoData<Matrix<mpq_class>> m = LoopInfoData<Matrix<mpq_class>>(
                nullSpace(exitMapIt.second.left),
                nullSpace(exitMapIt.second.right),
                nullSpace(exitMapIt.second.none));

            Matrix<mpz_class> nLeft(m.left.size());
            Matrix<mpz_class> nRight(m.right.size());
            Matrix<mpz_class> nNone(m.none.size());
            LoopInfoData<Matrix<mpz_class>> n =
                LoopInfoData<Matrix<mpz_class>>(nLeft, nRight, nNone);
            for (size_t i = 0; i < n.left.size(); ++i) {
                n.left.at(i) = ratToInt(m.left.at(i));
            }
            for (size_t i = 0; i < n.right.size(); ++i) {
                n.right.at(i) = ratToInt(m.right.at(i));
            }
            for (size_t i = 0; i < n.none.size(); ++i) {
                n.none.at(i) = ratToInt(m.none.at(i));
            }
            map[mark].insert(make_pair(exitMapIt.first, n));
        }
    }
    return map;
}

void dumpPolynomials(const PolynomialEquations &equationsMap,
                     const FreeVarsMap &freeVarsMap, size_t degree) {
    llvm::errs() << "------------------\n";
    PolynomialSolutions solutions = findSolutions(equationsMap);
    for (auto eqMapIt : solutions) {
        std::cerr << eqMapIt.first << ":\n";
        for (const auto &varName : freeVarsMap.at(eqMapIt.first)) {
            std::cerr << varName << "\t";
        }
        std::cerr << "constant\n";
        for (auto exitMapIt : eqMapIt.second) {
            std::cerr << "exit " << exitMapIt.first.get_str() << "\n";
            std::cerr << "left loop\n";
            dumpMatrix(exitMapIt.second.left);
            std::cerr << "right loop\n";
            dumpMatrix(exitMapIt.second.right);
            std::cerr << "synced\n";
            dumpMatrix(exitMapIt.second.none);
        }
    }
}

SharedSMTRef makeEquation(const vector<mpz_class> &eq,
                          const vector<string> &freeVars, size_t degree) {
    vector<SharedSMTRef> left;
    vector<SharedSMTRef> right;
    vector<SharedSMTRef> polynomialTerms;
    for (size_t i = 1; i <= degree; ++i) {
        auto kCombinations = polynomialTermsOfDegree(freeVars, i);
        for (auto vec : kCombinations) {
            multiset<string> vars;
            vars.insert(vec.begin(), vec.end());
            vector<SharedSMTRef> args;
            for (auto var : vars) {
                args.push_back(smt::stringExpr(var));
            }
            if (args.size() == 1) {
                polynomialTerms.push_back(args.front());
            } else {
                polynomialTerms.push_back(make_shared<Op>("*", args));
            }
        }
    }
    assert(polynomialTerms.size() + 1 == eq.size());
    for (size_t i = 0; i < polynomialTerms.size(); ++i) {
        if (eq.at(i) > 0) {
            if (eq.at(i) == 1) {
                left.push_back(polynomialTerms.at(i));
            } else {
                left.push_back(makeBinOp("*",
                                         smt::stringExpr(eq.at(i).get_str()),
                                         polynomialTerms.at(i)));
            }
        } else if (eq.at(i) < 0) {
            mpz_class inv = -eq.at(i);
            if (inv == 1) {
                right.push_back(polynomialTerms.at(i));
            } else {
                right.push_back(makeBinOp("*", smt::stringExpr(inv.get_str()),
                                          polynomialTerms.at(i)));
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
                                     const vector<string> &freeVars,
                                     size_t degree) {
    vector<SharedSMTRef> conjunction;
    for (const auto &vec : solution) {
        conjunction.push_back(makeEquation(vec, freeVars, degree));
    }
    if (conjunction.size() == 0) {
        return smt::stringExpr("false");
    } else {
        return make_shared<Op>("and", conjunction);
    }
}

SharedSMTRef
makeBoundsDefinitions(const map<string, Bound<Optional<VarIntVal>>> &bounds) {
    vector<SharedSMTRef> constraints;
    for (auto mapIt : bounds) {
        if (mapIt.second.lower.hasValue()) {
            constraints.push_back(makeBinOp(
                "<=", mapIt.second.lower.getValue().get_str(), mapIt.first));
        }
        if (mapIt.second.upper.hasValue()) {
            constraints.push_back(smt::makeBinOp(
                "<=", mapIt.first, mapIt.second.upper.getValue().get_str()));
        }
    }
    return make_shared<Op>("and", constraints);
}

map<int, SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const BoundsMap &bounds,
                         const FreeVarsMap &freeVarsMap, size_t degree) {
    map<int, SharedSMTRef> definitions;
    for (auto mapIt : solutions) {
        int mark = mapIt.first;
        vector<SortedVar> args;
        for (auto &var : freeVarsMap.at(mark)) {
            args.push_back(SortedVar(var, "Int"));
        }
        vector<SharedSMTRef> exitClauses;
        for (auto exitIt : mapIt.second) {
            SharedSMTRef left = makeInvariantDefinition(
                exitIt.second.left, freeVarsMap.at(mark), degree);
            SharedSMTRef right = makeInvariantDefinition(
                exitIt.second.right, freeVarsMap.at(mark), degree);
            SharedSMTRef none = makeInvariantDefinition(
                exitIt.second.none, freeVarsMap.at(mark), degree);
            vector<SharedSMTRef> invariantDisjunction = {left, right, none};
            SharedSMTRef invariant =
                make_shared<Op>("or", invariantDisjunction);
            exitClauses.push_back(invariant);
            // if (bounds.find(mark) != bounds.end()) {
            //     invariant =
            //         makeBinOp("and", invariant,
            //                   makeBoundsDefinitions(bounds.at(mark)));
            // }
        }
        string invariantName = "INV_MAIN_" + std::to_string(mark);
        if (ImplicationsFlag) {
            invariantName += "_INFERRED";
        }
        definitions[mark] =
            make_shared<FunDef>(invariantName, args, "Bool",
                                std::make_shared<Op>("or", exitClauses));
    }
    return definitions;
}

void instantiateBounds(map<int, map<string, Bound<VarIntVal>>> &boundsMap,
                       const FreeVarsMap &freeVars, MatchInfo match) {
    VarMap<string> variables;
    variables.insert(match.steps.first.state.variables.begin(),
                     match.steps.first.state.variables.end());
    variables.insert(match.steps.second.state.variables.begin(),
                     match.steps.second.state.variables.end());
    for (auto var : freeVars.at(match.mark)) {
        VarIntVal val = variables.at(var)->unsafeIntVal();
        if (boundsMap[match.mark].find(var) == boundsMap[match.mark].end()) {
            boundsMap.at(match.mark)
                .insert(make_pair(var, Bound<VarIntVal>(val, val)));
        } else {
            // Update bounds
            boundsMap.at(match.mark).at(var).lower =
                std::min(boundsMap.at(match.mark).at(var).lower, val);
            boundsMap.at(match.mark).at(var).upper =
                std::max(boundsMap.at(match.mark).at(var).upper, val);
        }
    }
}

BoundsMap updateBounds(
    BoundsMap accumulator,
    const std::map<int, std::map<std::string, Bound<VarIntVal>>> &update) {
    for (auto updateIt : update) {
        int mark = updateIt.first;
        for (auto varIt : updateIt.second) {
            if (accumulator[mark].find(varIt.first) ==
                accumulator[mark].end()) {
                // copy the bounds
                accumulator[mark].insert(make_pair(
                    varIt.first, Bound<Optional<VarIntVal>>(
                                     varIt.second.lower, varIt.second.upper)));
            } else {
                // We are only interested in bounds that are the same in all
                // iterations
                // Other bounds are probably false positives
                if (accumulator.at(mark).at(varIt.first).lower.hasValue() &&
                    accumulator.at(mark).at(varIt.first).lower.getValue() !=
                        varIt.second.lower) {
                    // delete lower bound
                    accumulator.at(mark).at(varIt.first).lower =
                        Optional<VarIntVal>();
                }
                if (accumulator.at(mark).at(varIt.first).upper.hasValue() &&
                    accumulator.at(mark).at(varIt.first).upper.getValue() !=
                        varIt.second.upper) {
                    accumulator.at(mark).at(varIt.first).upper =
                        Optional<VarIntVal>();
                }
            }
        }
    }
    return accumulator;
}

void dumpBounds(const BoundsMap &bounds) {
    std::cerr << "Bounds\n";
    for (auto markMapIt : bounds) {
        std::cerr << markMapIt.first << ":\n";
        for (auto varIt : markMapIt.second) {
            if (varIt.second.lower.hasValue()) {
                std::cerr << varIt.second.lower.getValue().get_str() << " <= ";
            }
            if (varIt.second.lower.hasValue() ||
                varIt.second.upper.hasValue()) {
                std::cerr << varIt.first;
            }
            if (varIt.second.upper.hasValue()) {
                std::cerr << " <= " << varIt.second.upper.getValue().get_str();
            }
            if (varIt.second.lower.hasValue() ||
                varIt.second.upper.hasValue()) {
                std::cerr << "\n";
            }
        }
    }
}

map<int, map<ExitIndex, LoopInfoData<set<MonoPair<string>>>>>
extractEqualities(const PolynomialEquations &polynomialEquations,
                  const vector<string> &freeVars) {
    map<int, map<ExitIndex, LoopInfoData<set<MonoPair<string>>>>> result;
    for (auto mapIt : polynomialEquations) {
        int mark = mapIt.first;
        for (auto exitIndex : mapIt.second) {
            result[mark].insert(
                make_pair(exitIndex.first,
                          LoopInfoData<set<MonoPair<string>>>({}, {}, {})));
            for (size_t i = 0; i < freeVars.size(); ++i) {
                for (size_t j = i + 1; j < freeVars.size(); ++j) {
                    vector<mpq_class> test(freeVars.size(), 0);
                    test.at(i) = 1;
                    test.at(j) = -1;
                    string firstVar = freeVars.at(i);
                    string secondVar = freeVars.at(j);
                    if (isZero(
                            matrixTimesVector(exitIndex.second.left, test))) {
                        result.at(mark)
                            .at(exitIndex.first)
                            .left.insert(makeMonoPair(firstVar, secondVar));
                        result.at(mark)
                            .at(exitIndex.first)
                            .left.insert(makeMonoPair(secondVar, firstVar));
                    }
                    if (isZero(
                            matrixTimesVector(exitIndex.second.right, test))) {
                        result.at(mark)
                            .at(exitIndex.first)
                            .right.insert(makeMonoPair(firstVar, secondVar));
                        result.at(mark)
                            .at(exitIndex.first)
                            .right.insert(makeMonoPair(secondVar, firstVar));
                    }
                    if (isZero(
                            matrixTimesVector(exitIndex.second.none, test))) {
                        result.at(mark)
                            .at(exitIndex.first)
                            .none.insert(makeMonoPair(firstVar, secondVar));
                        result.at(mark)
                            .at(exitIndex.first)
                            .none.insert(makeMonoPair(secondVar, firstVar));
                    }
                }
            }
        }
    }
    return result;
}

void dumpLoopCounts(const LoopCountMap &loopCounts) {
    std::cerr << "----------\n";
    std::cerr << "LOOP COUNTS\n";
    for (auto mapIt : loopCounts) {
        std::cerr << mapIt.first << "\n";
        for (auto countIt : mapIt.second) {
            std::cerr << "\t" << countIt << "\n";
        }
    }
    std::cerr << "----------\n";
}
