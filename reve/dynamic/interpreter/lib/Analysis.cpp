#include "Analysis.h"

#include "Compat.h"
#include "HeapPattern.h"
#include "HeapPattern.h"
#include "Interpreter.h"
#include "Linear.h"
#include "MarkAnalysis.h"
#include "ModuleSMTGeneration.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Serialize.h"
#include "SerializeTraces.h"
#include "Unroll.h"

#include <fstream>
#include <iostream>
#include <regex>
#include <thread>

// I don't care about windows
#include <dirent.h>
#include <stdio.h>
#include <sys/stat.h>

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

static llvm::cl::opt<bool>
    MultinomialsFlag("multinomials", llvm::cl::desc("Use true multinomials"));
std::string InputFileFlag;
static llvm::cl::opt<std::string, true>
    InputFileFlagStorage("input",
                         llvm::cl::desc("Use the inputs in the passed file"),
                         llvm::cl::location(InputFileFlag));
static llvm::cl::opt<unsigned>
    DegreeFlag("degree", llvm::cl::desc("Degree of the polynomial invariants"),
               llvm::cl::init(1));
static llvm::cl::opt<bool> ImplicationsFlag(
    "implications",
    llvm::cl::desc("Add implications instead of replacing invariants"));
static llvm::cl::opt<unsigned>
    ThreadsFlag("j", llvm::cl::desc("The number of threads to use"),
                llvm::cl::init(1));
bool InstantiateStorage;
static llvm::cl::opt<bool, true>
    InstantiateFlag("instantiate", llvm::cl::desc("Instantiate arrays"),
                    llvm::cl::location(InstantiateStorage));
static llvm::cl::opt<bool> HeapFlag("heap", llvm::cl::desc("Activate heap"));
static llvm::cl::opt<bool>
    InvertFlag("invert",
               llvm::cl::desc("Check for satisfiability of negation"));

vector<SharedSMTRef>
driver(MonoPair<std::shared_ptr<llvm::Module>> modules,
       vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
       string mainFunctionName,
       vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
       FileOptions fileOpts) {
    SMTGenerationOpts::getInstance().BitVect = BoundedFlag;
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
    const auto funArgsPair =
        functionArgs(*preprocessedFunctions.getValue().first.fun,
                     *preprocessedFunctions.getValue().second.fun);
    const auto funArgs = funArgsPair.foldl<vector<smt::SortedVar>>(
        {},
        [](auto acc, auto args) {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });

    // Collect loop info
    LoopCountsAndMark loopCounts;
    iterateTracesInRange<LoopCountsAndMark>(
        functions, -50, 50, ThreadsFlag, loopCounts, mergeLoopCounts,
        [&nameMap](MonoPair<Call<const llvm::Value *>> calls,
                   LoopCountsAndMark &localLoopCounts) {
            analyzeExecution<const llvm::Value *>(
                calls, nameMap,
                [&localLoopCounts](MatchInfo<const llvm::Value *> matchInfo) {
                    findLoopCounts<const llvm::Value *>(localLoopCounts,
                                                        matchInfo);
                });
        });
    map<int, LoopTransformation> loopTransformations =
        findLoopTransformations(loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);

    // Peel and unroll loops
    applyLoopTransformation(preprocessedFunctions.getValue(),
                            loopTransformations, markMaps);

    // Run the interpreter on the unrolled code
    MergedAnalysisResults analysisResults;
    const MonoPair<PathMap> pathMaps =
        preprocessedFunctions.getValue().map<PathMap>(
            [](PreprocessedFunction fun) { return fun.results.paths; });
    smt::FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
    size_t degree = DegreeFlag;
    iterateTracesInRange<MergedAnalysisResults>(
        functions, -50, 50, ThreadsFlag, analysisResults, mergeAnalysisResults,
        [&nameMap, &freeVarsMap, &patterns,
         degree](MonoPair<Call<const llvm::Value *>> calls,
                 MergedAnalysisResults &localAnalysisResults) {
            analyzeExecution<const llvm::Value *>(
                calls, nameMap,
                [&localAnalysisResults, &freeVarsMap, degree,
                 &patterns](MatchInfo<const llvm::Value *> match) {
                    findLoopCounts<const llvm::Value *>(
                        localAnalysisResults.loopCounts, match);
                    populateEquationsMap(
                        localAnalysisResults.polynomialEquations, freeVarsMap,
                        match, degree);
                    populateHeapPatterns(
                        localAnalysisResults.heapPatternCandidates, patterns,
                        freeVarsMap, match);
                });
        });
    loopTransformations =
        findLoopTransformations(analysisResults.loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);
    dumpPolynomials(analysisResults.polynomialEquations, freeVarsMap);
    dumpHeapPatterns(analysisResults.heapPatternCandidates);

    auto invariantCandidates = makeInvariantDefinitions(
        findSolutions(analysisResults.polynomialEquations),
        analysisResults.heapPatternCandidates, freeVarsMap, DegreeFlag);
    if (ImplicationsFlag) {
        SMTGenerationOpts::initialize(
            mainFunctionName, HeapFlag, false, false, false, false, false,
            false, false, false, false, false, BoundedFlag, InvertFlag, {});
    } else {
        SMTGenerationOpts::initialize(mainFunctionName, HeapFlag, false, false,
                                      false, false, false, false, false, false,
                                      false, false, BoundedFlag, InvertFlag,
                                      invariantCandidates);
    }
    // TODO pass all functions
    vector<SharedSMTRef> clauses =
        generateSMT(modules, {preprocessedFunctions.getValue()}, fileOpts);
    // Remove check-sat and get-model
    clauses.pop_back();
    clauses.pop_back();
    if (ImplicationsFlag) {
        // Add the necessary implications
        for (auto invariantIt : invariantCandidates) {
            auto mark = invariantIt.first;
            if (mark < 0) {
                continue;
            }
            vector<SortedVar> args;
            vector<smt::SharedSMTRef> stringArgs;

            for (const auto &var : filterVars(1, freeVarsMap.at(mark))) {
                if (BoundedFlag) {
                    args.push_back(var);
                } else {
                    args.push_back(SortedVar(var.name, "Int"));
                }
                stringArgs.push_back(smt::stringExpr(var.name));
            }
            if (HeapFlag) {
                args.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
                if (InstantiateStorage) {
                    stringArgs.push_back(smt::stringExpr("i1"));
                    stringArgs.push_back(makeBinOp("select", "HEAP$1", "i1"));
                } else {
                    stringArgs.push_back(smt::stringExpr("HEAP$1"));
                }
            }

            for (auto var : filterVars(2, freeVarsMap.at(mark))) {
                if (BoundedFlag) {
                    args.push_back(var);
                } else {
                    args.push_back(SortedVar(var.name, "Int"));
                }
                stringArgs.push_back(smt::stringExpr(var.name));
            }
            if (HeapFlag) {
                args.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
                if (InstantiateStorage) {
                    stringArgs.push_back(smt::stringExpr("i2"));
                    stringArgs.push_back(makeBinOp("select", "HEAP$2", "i2"));
                } else {
                    stringArgs.push_back(smt::stringExpr("HEAP$2"));
                }
            }
            string invariantName = "INV_MAIN_" + std::to_string(mark);
            string candidateName = invariantName + "_INFERRED";
            SharedSMTRef candidate =
                make_shared<smt::Op>(candidateName, stringArgs);
            SharedSMTRef invariant =
                make_shared<smt::Op>(invariantName, stringArgs);
            if (InstantiateStorage) {
                vector<SortedVar> indices = {SortedVar("i1", "Int"),
                                             SortedVar("i2", "Int")};
                candidate = make_shared<smt::Forall>(indices, candidate);
                invariant = make_shared<smt::Forall>(indices, invariant);
            }
            SharedSMTRef impl = makeBinOp("=>", invariant, candidate);
            SharedSMTRef forall = make_shared<smt::Forall>(args, impl);
            clauses.push_back(invariantIt.second);
            clauses.push_back(make_shared<smt::Assert>(forall));
        }
    }
    clauses.push_back(make_shared<smt::CheckSat>());
    clauses.push_back(make_shared<smt::GetModel>());

    return clauses;
}

std::vector<smt::SharedSMTRef>
cegarDriver(MonoPair<std::shared_ptr<llvm::Module>> modules,
            vector<MonoPair<PreprocessedFunction>> preprocessedFuns,
            string mainFunctionName,
            vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
            FileOptions fileOpts) {
    SMTGenerationOpts::getInstance().BitVect = BoundedFlag;
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
    const auto funArgsPair =
        functionArgs(*preprocessedFunctions.getValue().first.fun,
                     *preprocessedFunctions.getValue().second.fun);
    const auto funArgs = funArgsPair.foldl<vector<smt::SortedVar>>(
        {},
        [](auto acc, auto args) {
            acc.insert(acc.end(), args.begin(), args.end());
            return acc;
        });

    // Run the interpreter on the unrolled code
    MergedAnalysisResults analysisResults;
    MonoPair<PathMap> pathMaps = preprocessedFunctions.getValue().map<PathMap>(
        [](PreprocessedFunction fun) { return fun.results.paths; });
    smt::FreeVarsMap freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
    size_t degree = DegreeFlag;
    ModelValues vals = initialModelValues(functions);
    auto instrNameMap = instructionNameMap(functions);
    do {
        int cexMark = static_cast<int>(vals.values.at("INV_INDEX").get_si());
        // reconstruct input from counterexample
        auto variableValues = getVarMapFromModel(
            instrNameMap, freeVarsMap.at(cexMark), vals.values);

        // dump new example
        std::cout << "---\nFound counterexample:\n";
        std::cout << "at invariant: " << cexMark << "\n";
        for (auto it : variableValues.first) {
            llvm::errs() << it.first->getName() << " "
                         << unsafeIntVal(it.second).asUnbounded().get_str()
                         << "\n";
        }
        for (auto it : variableValues.second) {
            llvm::errs() << it.first->getName() << " "
                         << unsafeIntVal(it.second).asUnbounded().get_str()
                         << "\n";
        }
        for (auto ar : vals.arrays) {
            std::cout << ar.first << "\n";
            std::cout << "background: " << ar.second.background << "\n";
            for (auto val : ar.second.vals) {
                std::cout << val.first << ":" << val.second << "\n";
            }
        }

        assert(markMaps.first.MarkToBlocksMap.at(cexMark).size() == 1);
        assert(markMaps.second.MarkToBlocksMap.at(cexMark).size() == 1);
        auto firstBlock = *markMaps.first.MarkToBlocksMap.at(cexMark).begin();
        auto secondBlock = *markMaps.second.MarkToBlocksMap.at(cexMark).begin();
        std::string tmp;
        // getline(std::cin, tmp);

        MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
            functions, variableValues, getHeapsFromModel(vals.arrays),
            getHeapBackgrounds(vals.arrays), {firstBlock, secondBlock}, 1000);
        // analyzeExecution<const llvm::Value *>(calls, nameMap, debugAnalysis);
        analyzeExecution<const llvm::Value *>(
            calls, nameMap, [&analysisResults, &freeVarsMap, degree,
                             &patterns](MatchInfo<const llvm::Value *> match) {
                findLoopCounts<const llvm::Value *>(analysisResults.loopCounts,
                                                    match);
                populateEquationsMap(analysisResults.polynomialEquations,
                                     freeVarsMap, match, degree);
                populateHeapPatterns(analysisResults.heapPatternCandidates,
                                     patterns, freeVarsMap, match);
            });
        map<int, LoopTransformation> loopTransformations =
            findLoopTransformations(analysisResults.loopCounts.loopCounts);
        dumpLoopTransformations(loopTransformations);

        // // Peel and unroll loops
        if (applyLoopTransformation(preprocessedFunctions.getValue(),
                                    loopTransformations, markMaps)) {
            // Reset data and start over
            analysisResults = MergedAnalysisResults();
            vals = initialModelValues(functions);
            // The paths have changed so we need to update the free variables
            pathMaps = preprocessedFunctions.getValue().map<PathMap>(
                [](PreprocessedFunction fun) { return fun.results.paths; });
            freeVarsMap = freeVars(pathMaps.first, pathMaps.second, funArgs, 0);
            instrNameMap = instructionNameMap(functions);
            std::cerr << "Transformed program, resetting inputs\n";
            continue;
        }

        auto invariantCandidates = makeInvariantDefinitions(
            findSolutions(analysisResults.polynomialEquations),
            analysisResults.heapPatternCandidates, freeVarsMap, DegreeFlag);

        SMTGenerationOpts::initialize(mainFunctionName, HeapFlag, false, false,
                                      false, false, false, false, false, false,
                                      false, false, false, true,
                                      invariantCandidates);
        vector<SharedSMTRef> clauses =
            generateSMT(modules, {preprocessedFunctions.getValue()}, fileOpts);
        char templateName[] = "/tmp/tmpsmt_XXXXXX.smt2";
        int tmpSMTFd = mkstemps(templateName, 5);
        string templateFileName(templateName);
        serializeSMT(clauses, false,
                     SerializeOpts(templateFileName, !InstantiateStorage, false,
                                   BoundedFlag, false));
        string command = "z3 " + templateFileName;
        FILE *out = popen(command.c_str(), "r");
        auto result = parseResult(out);
        pclose(out);
        unlink(templateName);
        close(tmpSMTFd);
        if (!result->isSat()) {
            break;
        }
        vals = parseValues(std::static_pointer_cast<Sat>(result)->model);
    } while (1 /* sat */);
    auto invariantCandidates = makeInvariantDefinitions(
        findSolutions(analysisResults.polynomialEquations),
        analysisResults.heapPatternCandidates, freeVarsMap, DegreeFlag);

    SMTGenerationOpts::initialize(
        mainFunctionName, HeapFlag, false, false, false, false, false, false,
        false, false, false, false, false, true, invariantCandidates);
    vector<SharedSMTRef> clauses =
        generateSMT(modules, {preprocessedFunctions.getValue()}, fileOpts);

    return clauses;
}

bool applyLoopTransformation(
    MonoPair<PreprocessedFunction> &functions,
    const map<int, LoopTransformation> &loopTransformations,
    const MonoPair<BidirBlockMarkMap> &marks) {
    bool modified = false;
    for (auto mapIt : loopTransformations) {
        switch (mapIt.second.type) {
        case LoopTransformType::Peel:
            if (mapIt.second.count == 0) {
                continue;
            }
            modified = true;
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
    return modified;
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

map<int, LoopTransformation> findLoopTransformations(LoopCountMap &map) {
    std::map<int, int32_t> peelCount;
    std::map<int, float> unrollQuotients;
    for (auto mapIt : map) {
        int mark = mapIt.first;
        for (auto sample : mapIt.second) {
            if (sample.first < 3 || sample.second < 3) {
                continue;
            }
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
        } else if (unrollQuotients.count(mark) > 0) {
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

vector<vector<string>> polynomialTermsOfDegree(vector<smt::SortedVar> variables,
                                               size_t degree) {
    if (MultinomialsFlag) {
        vector<vector<SortedVar>> res =
            kCombinationsWithRepetitions(variables, degree);
        vector<vector<string>> resString;
        for (const auto &vec : res) {
            vector<string> innerString;
            for (const auto &var : vec) {
                innerString.push_back(var.name);
            }
            resString.push_back(std::move(innerString));
        }
        return resString;
    } else {
        vector<vector<string>> terms;
        for (auto var : variables) {
            vector<string> term(degree, var.name);
            terms.push_back(term);
        }
        return terms;
    }
}

void populateEquationsMap(PolynomialEquations &polynomialEquations,
                          smt::FreeVarsMap freeVarsMap,
                          MatchInfo<const llvm::Value *> match, size_t degree) {
    VarMap<string> variables;
    for (auto varIt : match.steps.first->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    for (auto varIt : match.steps.second->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    vector<mpq_class> equation;
    for (size_t i = 1; i <= degree; ++i) {
        auto polynomialTerms =
            polynomialTermsOfDegree(freeVarsMap.at(match.mark), i);
        for (auto term : polynomialTerms) {
            mpz_class termVal = 1;
            for (auto var : term) {
                termVal *= unsafeIntVal(variables.at(var)).asUnbounded();
            }
            equation.push_back(termVal);
        }
    }
    // Add a constant at the end of each vector
    equation.push_back(1);
    ExitIndex exitIndex = 0;
    if (variables.count("exitIndex$1_" + std::to_string(match.mark)) == 1) {
        exitIndex = unsafeIntVal(variables.at("exitIndex$1_" +
                                              std::to_string(match.mark)))
                        .asUnbounded();
    } else if (variables.count("exitIndex$2_" + std::to_string(match.mark)) ==
               1) {
        exitIndex = unsafeIntVal(variables.at("exitIndex$2_" +
                                              std::to_string(match.mark)))
                        .asUnbounded();
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

void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    smt::FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match) {
    VarMap<const llvm::Value *> variables(match.steps.first->state.variables);
    variables.insert(match.steps.second->state.variables.begin(),
                     match.steps.second->state.variables.end());
    // TODO don’t copy heaps
    MonoPair<Heap> heaps = makeMonoPair(match.steps.first->state.heap,
                                        match.steps.second->state.heap);
    ExitIndex exitIndex = 0;
    for (auto var : variables) {
        if (var.first->getName() ==
            "exitIndex$1" + std::to_string(match.mark)) {
            exitIndex = unsafeIntVal(var.second).asUnbounded();
        } else if (var.first->getName() ==
                   "exitIndex$2" + std::to_string(match.mark)) {
            exitIndex = unsafeIntVal(var.second).asUnbounded();
        }
    }
    bool newCandidates =
        heapPatternCandidates[match.mark].count(exitIndex) == 0;
    if (!newCandidates) {
        switch (match.loopInfo) {
        case LoopInfo::Left:
            newCandidates = !heapPatternCandidates.at(match.mark)
                                 .at(exitIndex)
                                 .left.hasValue();
            break;
        case LoopInfo::Right:
            newCandidates = !heapPatternCandidates.at(match.mark)
                                 .at(exitIndex)
                                 .right.hasValue();
            break;
        case LoopInfo::None:
            newCandidates = !heapPatternCandidates.at(match.mark)
                                 .at(exitIndex)
                                 .none.hasValue();
            break;
        }
    }
    if (newCandidates) {
        list<shared_ptr<HeapPattern<const llvm::Value *>>> candidates;
        for (auto pat : patterns) {
            auto newCandidates =
                pat->instantiate(freeVarsMap.at(match.mark), variables, heaps);
            candidates.splice(candidates.end(), newCandidates);
        }
        heapPatternCandidates.at(match.mark)
            .insert(make_pair(exitIndex,
                              LoopInfoData<Optional<HeapPatternCandidates>>(
                                  Optional<HeapPatternCandidates>(),
                                  Optional<HeapPatternCandidates>(),
                                  Optional<HeapPatternCandidates>())));
        switch (match.loopInfo) {
        case LoopInfo::Left:
            assert(!heapPatternCandidates.at(match.mark)
                        .at(exitIndex)
                        .left.hasValue());
            heapPatternCandidates.at(match.mark).at(exitIndex).left =
                std::move(candidates);
            break;
        case LoopInfo::Right:
            assert(!heapPatternCandidates.at(match.mark)
                        .at(exitIndex)
                        .right.hasValue());
            heapPatternCandidates.at(match.mark).at(exitIndex).right =
                std::move(candidates);
            break;
        case LoopInfo::None:
            assert(!heapPatternCandidates.at(match.mark)
                        .at(exitIndex)
                        .none.hasValue());
            heapPatternCandidates.at(match.mark).at(exitIndex).none =
                std::move(candidates);
            break;
        }
    } else {
        HeapPatternCandidates *patterns = nullptr;
        switch (match.loopInfo) {
        case LoopInfo::Left:
            patterns = &heapPatternCandidates.at(match.mark)
                            .at(exitIndex)
                            .left.getValue();
            break;
        case LoopInfo::Right:
            patterns = &heapPatternCandidates.at(match.mark)
                            .at(exitIndex)
                            .right.getValue();
            break;
        case LoopInfo::None:
            patterns = &heapPatternCandidates.at(match.mark)
                            .at(exitIndex)
                            .none.getValue();
            break;
        }
        auto listIt = patterns->begin();
        while (listIt != patterns->end()) {
            if (!(*listIt)->matches(variables, heaps)) {
                listIt = patterns->erase(listIt);
            } else {
                ++listIt;
            }
        }
    }
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

bool normalMarkBlock(const BlockNameMap &map, const BlockName &blockName) {
    auto it = map.find(blockName);
    if (it == map.end()) {
        return false;
    }
    return it->second.count(ENTRY_MARK) == 0;
}

void debugAnalysis(MatchInfo<const llvm::Value *> match) {
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
    std::cerr << match.steps.first->toJSON([](auto x) { return x->getName(); })
                     .dump(4)
              << std::endl;
    std::cerr << "Second state:" << std::endl;
    std::cerr << match.steps.second->toJSON([](auto x) { return x->getName(); })
                     .dump(4)
              << std::endl;
    std::cerr << std::endl << std::endl;
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
                     const smt::FreeVarsMap &freeVarsMap) {
    llvm::errs() << "------------------\n";
    PolynomialSolutions solutions = findSolutions(equationsMap);
    for (auto eqMapIt : solutions) {
        std::cerr << eqMapIt.first << ":\n";
        for (const auto &varName : freeVarsMap.at(eqMapIt.first)) {
            std::cerr << varName.name << "\t";
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

void dumpHeapPatterns(const HeapPatternCandidatesMap &heapPatternsMap) {
    llvm::errs() << "------------------\n";
    for (auto eqMapIt : heapPatternsMap) {
        std::cerr << eqMapIt.first << ":\n";
        for (auto exitMapIt : eqMapIt.second) {
            std::cerr << "exit " << exitMapIt.first.get_str() << "\n";
            if (exitMapIt.second.left.hasValue()) {
                std::cerr << "left loop\n";
                for (auto pat : exitMapIt.second.left.getValue()) {
                    pat->dump(std::cerr);
                    std::cerr << "\n";
                }
            }
            if (exitMapIt.second.right.hasValue()) {
                std::cerr << "right loop\n";
                for (auto pat : exitMapIt.second.right.getValue()) {
                    pat->dump(std::cerr);
                    std::cerr << "\n";
                }
            }
            if (exitMapIt.second.none.hasValue()) {
                std::cerr << "synced\n";
                for (auto pat : exitMapIt.second.none.getValue()) {
                    pat->dump(std::cerr);
                    std::cerr << "\n";
                }
            }
        }
    }
}

SharedSMTRef makeEquation(const vector<mpz_class> &eq,
                          const vector<smt::SortedVar> &freeVars,
                          size_t degree) {
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
        std::string mulName = BoundedFlag ? "bvmul" : "*";
        if (eq.at(i) > 0) {
            if (eq.at(i) == 1) {
                left.push_back(polynomialTerms.at(i));
            } else {
                left.push_back(makeBinOp(mulName,
                                         intToSMT(eq.at(i).get_str(), 32),
                                         polynomialTerms.at(i)));
            }
        } else if (eq.at(i) < 0) {
            mpz_class inv = -eq.at(i);
            if (inv == 1) {
                right.push_back(polynomialTerms.at(i));
            } else {
                right.push_back(makeBinOp(mulName, intToSMT(inv.get_str(), 32),
                                          polynomialTerms.at(i)));
            }
        }
    }
    if (eq.back() > 0) {
        left.push_back(intToSMT(eq.back().get_str(), 32));
    } else if (eq.back() < 0) {
        mpz_class inv = -eq.back();
        right.push_back(intToSMT(inv.get_str(), 32));
    }
    SharedSMTRef leftSide = nullptr;
    if (left.size() == 0) {
        leftSide = intToSMT("0", 32);
    } else if (left.size() == 1) {
        leftSide = left.front();
    } else {
        if (BoundedFlag) {
            leftSide = make_shared<Op>("bvadd", left);
        } else {
            leftSide = make_shared<Op>("+", left);
        }
    }
    SharedSMTRef rightSide = nullptr;
    if (right.size() == 0) {
        rightSide = intToSMT("0", 32);
    } else if (right.size() == 1) {
        rightSide = right.front();
    } else {
        if (BoundedFlag) {
            rightSide = make_shared<Op>("bvadd", right);
        } else {
            rightSide = make_shared<Op>("+", right);
        }
    }
    return makeBinOp("=", leftSide, rightSide);
}

SharedSMTRef makeInvariantDefinition(const vector<vector<mpz_class>> &solution,
                                     const HeapPatternCandidates &candidates,
                                     const vector<SortedVar> &freeVars,
                                     size_t degree) {
    vector<SharedSMTRef> conjunction;
    for (const auto &vec : solution) {
        conjunction.push_back(makeEquation(vec, freeVars, degree));
    }
    for (const auto &candidate : candidates) {
        if (InstantiateStorage) {
            conjunction.push_back(
                candidate->negationNormalForm()->instantiate()->toSMT());
        } else {
            conjunction.push_back(candidate->toSMT());
        }
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
                         const HeapPatternCandidatesMap &patterns,
                         const smt::FreeVarsMap &freeVarsMap, size_t degree) {
    map<int, SharedSMTRef> definitions;
    for (auto mapIt : solutions) {
        int mark = mapIt.first;
        vector<SortedVar> args;
        vector<string> stringArgs;
        for (const auto &var : filterVars(1, freeVarsMap.at(mark))) {
            if (BoundedFlag) {
                args.push_back(SortedVar(var.name, var.type));
            } else {
                args.push_back(SortedVar(var.name, "Int"));
            }
        }
        if (HeapFlag) {
            if (InstantiateStorage) {
                args.push_back(SortedVar("i1", "Int"));
                args.push_back(SortedVar("heap1", "Int"));
            } else {
                args.push_back(SortedVar("HEAP$1", "(Array Int Int)"));
            }
        }

        for (auto var : filterVars(2, freeVarsMap.at(mark))) {
            if (BoundedFlag) {
                args.push_back(SortedVar(var.name, var.type));
            } else {
                args.push_back(SortedVar(var.name, "Int"));
            }
        }
        if (HeapFlag) {
            if (InstantiateStorage) {
                args.push_back(SortedVar("i2", "Int"));
                args.push_back(SortedVar("heap2", "Int"));
            } else {
                args.push_back(SortedVar("HEAP$2", "(Array Int Int)"));
            }
        }
        vector<SharedSMTRef> exitClauses;
        for (auto exitIt : mapIt.second) {
            ExitIndex exit = exitIt.first;
            // TODO Figure out why we get to a point where these maps are empty
            SharedSMTRef left = makeInvariantDefinition(
                exitIt.second.left,
                patterns.count(mark) > 0 && patterns.at(mark).count(exit) > 0 &&
                        patterns.at(mark).at(exit).left.hasValue()
                    ? patterns.at(mark).at(exit).left.getValue()
                    : HeapPatternCandidates(),
                freeVarsMap.at(mark), degree);
            SharedSMTRef right = makeInvariantDefinition(
                exitIt.second.right,
                patterns.count(mark) > 0 && patterns.at(mark).count(exit) > 0 &&
                        patterns.at(mark).at(exit).right.hasValue()
                    ? patterns.at(mark).at(exit).right.getValue()
                    : HeapPatternCandidates(),
                freeVarsMap.at(mark), degree);
            SharedSMTRef none = makeInvariantDefinition(
                exitIt.second.none,
                patterns.count(mark) > 0 && patterns.at(mark).count(exit) > 0 &&
                        patterns.at(mark).at(exit).none.hasValue()
                    ? patterns.at(mark).at(exit).none.getValue()
                    : HeapPatternCandidates(),
                freeVarsMap.at(mark), degree);
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
        definitions[mark] = make_shared<FunDef>(
            invariantName, args, "Bool", make_shared<Op>("or", exitClauses));
    }
    return definitions;
}

void instantiateBounds(map<int, map<string, Bound<VarIntVal>>> &boundsMap,
                       const smt::FreeVarsMap &freeVars,
                       MatchInfo<string> match) {
    VarMap<string> variables;
    variables.insert(match.steps.first->state.variables.begin(),
                     match.steps.first->state.variables.end());
    variables.insert(match.steps.second->state.variables.begin(),
                     match.steps.second->state.variables.end());
    for (const auto &var : freeVars.at(match.mark)) {
        VarIntVal val = unsafeIntVal(variables.at(var.name));
        if (boundsMap[match.mark].find(var.name) ==
            boundsMap[match.mark].end()) {
            boundsMap.at(match.mark)
                .insert(make_pair(var.name, Bound<VarIntVal>(val, val)));
        } else {
            // Update bounds
            boundsMap.at(match.mark).at(var.name).lower =
                std::min(boundsMap.at(match.mark).at(var.name).lower, val);
            boundsMap.at(match.mark).at(var.name).upper =
                std::max(boundsMap.at(match.mark).at(var.name).upper, val);
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

std::map<const llvm::Value *, VarVal> getVarMap(const llvm::Function *fun,
                                                std::vector<mpz_class> vals) {
    std::map<const llvm::Value *, VarVal> variableValues;
    auto argIt = fun->arg_begin();
    for (size_t i = 0; i < vals.size(); ++i) {
        const llvm::Value *arg = &*argIt;
        // Pointers are always unbounded
        if (BoundedFlag && arg->getType()->isIntegerTy()) {
            variableValues.insert(
                {arg,
                 Integer(makeBoundedInt(arg->getType()->getIntegerBitWidth(),
                                        vals[i].get_si()))});
        } else if (arg->getType()->isPointerTy()) {
            variableValues.insert({arg, Integer(vals[i]).asPointer()});
        } else {
            variableValues.insert({arg, Integer(vals[i])});
        }
        ++argIt;
    }
    assert(argIt == fun->arg_end());
    return variableValues;
}

std::map<std::string, const llvm::Value *>
instructionNameMap(const llvm::Function *fun) {
    std::map<std::string, const llvm::Value *> nameMap;
    for (const auto &arg : fun->args()) {
        nameMap.insert({arg.getName(), &arg});
    }
    for (const auto &bb : *fun) {
        for (const auto &instr : bb) {
            if (!instr.getName().empty()) {
                nameMap.insert({instr.getName(), &instr});
            }
        }
    }
    return nameMap;
}

std::map<std::string, const llvm::Value *>
instructionNameMap(MonoPair<const llvm::Function *> funs) {
    std::map<std::string, const llvm::Value *> nameMap =
        instructionNameMap(funs.first);
    std::map<std::string, const llvm::Value *> nameMap2 =
        instructionNameMap(funs.second);
    nameMap.insert(nameMap2.begin(), nameMap2.end());
    return nameMap;
}

MonoPair<std::map<const llvm::Value *, VarVal>> getVarMapFromModel(
    std::map<std::string, const llvm::Value *> instructionNameMap,
    std::vector<smt::SortedVar> freeVars,
    std::map<std::string, mpz_class> vals) {
    MonoPair<std::map<const llvm::Value *, VarVal>> variableValues =
        makeMonoPair<std::map<const llvm::Value *, VarVal>>({}, {});
    for (const auto &var : freeVars) {
        mpz_class val = vals.at(var.name + "_old");
        const llvm::Value *instr = instructionNameMap.at(var.name);
        if (varBelongsTo(var.name, 1)) {
            variableValues.first.insert({instr, Integer(val)});
        } else {
            variableValues.second.insert({instr, Integer(val)});
        }
    }
    return variableValues;
}

Heap getHeapFromModel(const ArrayVal &ar) {
    Heap result;
    for (auto it : ar.vals) {
        result.insert({Integer(it.first), Integer(it.second)});
    }
    return result;
}

MonoPair<Heap> getHeapsFromModel(std::map<std::string, ArrayVal> arrays) {
    if (!HeapFlag) {
        return {{}, {}};
    }
    return {getHeapFromModel(arrays.at("HEAP$1_old")),
            getHeapFromModel(arrays.at("HEAP$2_old"))};
}

MonoPair<Integer> getHeapBackgrounds(std::map<std::string, ArrayVal> arrays) {
    if (!HeapFlag) {
        return {Integer(mpz_class(0)), Integer(mpz_class(0))};
    }
    return {Integer(arrays.at("HEAP$1_old").background),
            Integer(arrays.at("HEAP$2_old").background)};
}

Heap randomHeap(const llvm::Function &fun,
                const std::map<const llvm::Value *, VarVal> &variableValues,
                int lengthBound, int valLowerBound, int valUpperBound,
                unsigned int *seedp) {
    // We place an array with a random length <= lengthBound with random values
    // >= valLowerBound and <= valUpperBound at each pointer argument
    Heap heap;
    for (const auto &arg : fun.args()) {
        if (arg.getType()->isPointerTy()) {
            VarIntVal arrayStart = unsafeIntVal(variableValues.at(&arg));
            unsigned int length =
                static_cast<unsigned int>(rand_r(seedp) % (lengthBound + 1));
            for (unsigned int i = 0; i <= length; ++i) {
                int val =
                    (rand_r(seedp) % (valUpperBound - valLowerBound + 1)) +
                    valLowerBound;
                if (BoundedFlag) {
                    heap.insert(
                        {arrayStart.asPointer() +
                             Integer(mpz_class(i)).asPointer(),
                         Integer(makeBoundedInt(HeapElemSizeFlag, val))});
                } else {
                    heap.insert({arrayStart.asPointer() +
                                     Integer(mpz_class(i)).asPointer(),
                                 Integer(mpz_class(val))});
                }
            }
        }
    }
    return heap;
}

LoopCountsAndMark mergeLoopCounts(LoopCountsAndMark counts1,
                                  LoopCountsAndMark counts2) {
    LoopCountsAndMark result = counts1;
    for (auto it : counts2.loopCounts) {
        result.loopCounts[it.first].insert(result.loopCounts[it.first].end(),
                                           it.second.begin(), it.second.end());
    }
    return result;
}

MergedAnalysisResults mergeAnalysisResults(MergedAnalysisResults res1,
                                           MergedAnalysisResults res2) {
    MergedAnalysisResults result;
    result.loopCounts = mergeLoopCounts(res1.loopCounts, res2.loopCounts);
    result.polynomialEquations = mergePolynomialEquations(
        res1.polynomialEquations, res2.polynomialEquations);
    result.heapPatternCandidates = mergeHeapPatternMaps(
        res1.heapPatternCandidates, res2.heapPatternCandidates);
    return result;
}

PolynomialEquations mergePolynomialEquations(PolynomialEquations eq1,
                                             PolynomialEquations eq2) {
    PolynomialEquations result = eq1;
    for (auto it : eq2) {
        int mark = it.first;
        for (auto innerIt : it.second) {
            ExitIndex exit = innerIt.first;
            for (auto &vec : innerIt.second.left) {
                std::vector<std::vector<mpq_class>> newVec =
                    result[mark][exit].left;
                newVec.push_back(vec);
                if (linearlyIndependent(newVec)) {
                    result.at(mark).at(exit).left = newVec;
                }
            }
            for (auto &vec : innerIt.second.right) {
                std::vector<std::vector<mpq_class>> newVec =
                    result[mark][exit].right;
                newVec.push_back(vec);
                if (linearlyIndependent(newVec)) {
                    result.at(mark).at(exit).right = newVec;
                }
            }
            for (auto &vec : innerIt.second.none) {
                std::vector<std::vector<mpq_class>> newVec =
                    result[mark][exit].none;
                newVec.push_back(vec);
                if (linearlyIndependent(newVec)) {
                    result.at(mark).at(exit).none = newVec;
                }
            }
        }
    }
    return result;
}

HeapPatternCandidatesMap mergeHeapPatternMaps(HeapPatternCandidatesMap cand1,
                                              HeapPatternCandidatesMap cand2) {
    HeapPatternCandidatesMap result = cand1;
    for (auto &it : result) {
        int mark = it.first;
        for (auto &exitIt : it.second) {
            ExitIndex exit = exitIt.first;
            if (cand2.count(mark) > 0 && cand2.at(mark).count(exit) > 0) {
                zipWith<llvm::Optional<HeapPatternCandidates>,
                        llvm::Optional<HeapPatternCandidates>>(
                    exitIt.second, cand2.at(mark).at(exit),
                    [](auto &resultPat, auto &otherPat) {
                        if (resultPat.hasValue()) {
                            if (otherPat.hasValue()) {
                                resultPat = mergeHeapPatternCandidates(
                                    resultPat.getValue(), otherPat.getValue());
                            }
                        } else {
                            resultPat = otherPat;
                        }
                    });
            }
        }
    }
    for (auto it : cand2) {
        int mark = it.first;
        for (auto exitIt : it.second) {
            ExitIndex exit = exitIt.first;
            if (result.count(mark) == 0 || result.at(mark).count(exit) == 0) {
                result[mark][exit] = exitIt.second;
            }
        }
    }
    return result;
}

HeapPatternCandidates
mergeHeapPatternCandidates(HeapPatternCandidates candidates1,
                           HeapPatternCandidates candidates2) {
    auto it = candidates1.begin();
    while (it != candidates1.end()) {
        bool breaked = false;
        for (const auto &pat : candidates2) {
            if ((*it)->equalTo(*pat)) {
                breaked = true;
                break;
            }
        }
        if (!breaked) {
            it = candidates1.erase(it);
        } else {
            ++it;
        }
    }
    return candidates1;
}

ModelValues initialModelValues(MonoPair<const llvm::Function *> funs) {
    ModelValues vals;
    vals.arrays.insert({"HEAP$1_old", {0, {}}});
    vals.arrays.insert({"HEAP$2_old", {0, {}}});
    for (const auto &arg : funs.first->args()) {
        vals.values.insert({std::string(arg.getName()) + "_old", 5});
    }
    for (const auto &arg : funs.second->args()) {
        vals.values.insert({std::string(arg.getName()) + "_old", 5});
    }
    vals.values.insert({"INV_INDEX", ENTRY_MARK});
    return vals;
}
