/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Analysis.h"

#include "Compat.h"
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

using std::make_unique;
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

using namespace smt;
using namespace std::placeholders;

static std::unique_ptr<ConstantInt> smtFromMpz(unsigned bitWidth, mpz_class i) {
    return std::make_unique<ConstantInt>(
        llvm::APInt(bitWidth, i.get_str(), 10));
}

static llreve::cl::opt<bool>
    MultinomialsFlag("multinomials", llreve::cl::desc("Use true multinomials"));
static llreve::cl::opt<bool>
    PrettyFlag("pretty", llreve::cl::desc("Pretty print intermediate output"));
std::string InputFileFlag;
static llreve::cl::opt<std::string, true>
    InputFileFlagStorage("input",
                         llreve::cl::desc("Use the inputs in the passed file"),
                         llreve::cl::location(InputFileFlag));
static llreve::cl::opt<unsigned>
    DegreeFlag("degree",
               llreve::cl::desc("Degree of the polynomial invariants"),
               llreve::cl::init(1));
static llreve::cl::opt<bool> ImplicationsFlag(
    "implications",
    llreve::cl::desc("Add implications instead of replacing invariants"));
static llreve::cl::opt<unsigned>
    ThreadsFlag("j", llreve::cl::desc("The number of threads to use"),
                llreve::cl::init(1));

vector<SharedSMTRef>
driver(MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
       vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
       FileOptions fileOpts) {
    auto functionPair = SMTGenerationOpts::getInstance().MainFunctions;
    const MonoPair<BidirBlockMarkMap> markMaps =
        getBlockMarkMaps(functionPair, analysisResults);
    MonoPair<BlockNameMap> nameMap = markMaps.map<BlockNameMap>(blockNameMap);
    const auto funArgsPair =
        getFunctionArguments(functionPair, analysisResults);
    const auto funArgs = concat(funArgsPair);

    // Collect loop info
    LoopCountsAndMark loopCounts;
    iterateTracesInRange<LoopCountsAndMark>(
        functionPair, -50, 50, ThreadsFlag, loopCounts, mergeLoopCounts,
        [&nameMap](MonoPair<Call<const llvm::Value *>> calls,
                   LoopCountsAndMark &localLoopCounts) {
            analyzeExecution<const llvm::Value *>(
                calls, nameMap,
                [&localLoopCounts](MatchInfo<const llvm::Value *> matchInfo) {
                    findLoopCounts<const llvm::Value *>(localLoopCounts,
                                                        matchInfo);
                });
        });
    auto loopTransformations = findLoopTransformations(loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);

    // Peel and unroll loops
    applyLoopTransformation(functionPair, analysisResults, loopTransformations,
                            markMaps);

    // Run the interpreter on the unrolled code
    MergedAnalysisResults dynamicAnalysisResults;
    const MonoPair<PathMap> pathMaps =
        getPathMaps(functionPair, analysisResults);
    FreeVarsMap freeVarsMap = getFreeVarsMap(functionPair, analysisResults);
    size_t degree = DegreeFlag;
    iterateTracesInRange<MergedAnalysisResults>(
        functionPair, -50, 50, ThreadsFlag, dynamicAnalysisResults,
        mergeAnalysisResults, [&nameMap, &freeVarsMap, &patterns, degree](
                                  MonoPair<Call<const llvm::Value *>> calls,
                                  MergedAnalysisResults &localAnalysisResults) {
            analyzeExecution<const llvm::Value *>(
                calls, nameMap,
                [&localAnalysisResults, &freeVarsMap, degree,
                 &patterns](MatchInfo<const llvm::Value *> match) {
                    ExitIndex exitIndex = getExitIndex(match);
                    findLoopCounts<const llvm::Value *>(
                        localAnalysisResults.loopCounts, match);
                    populateEquationsMap(
                        localAnalysisResults.polynomialEquations, freeVarsMap,
                        match, exitIndex, degree);
                    populateHeapPatterns(
                        localAnalysisResults.heapPatternCandidates, patterns,
                        freeVarsMap, match, exitIndex);
                });
        });
    loopTransformations =
        findLoopTransformations(dynamicAnalysisResults.loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);
    dumpPolynomials(dynamicAnalysisResults.polynomialEquations, freeVarsMap);
    dumpHeapPatterns(dynamicAnalysisResults.heapPatternCandidates);

    auto invariantCandidates = makeInvariantDefinitions(
        findSolutions(dynamicAnalysisResults.polynomialEquations),
        dynamicAnalysisResults.heapPatternCandidates, freeVarsMap, DegreeFlag);
    if (!ImplicationsFlag) {
        SMTGenerationOpts::getInstance().Invariants = invariantCandidates;
    }
    // TODO pass all functions
    vector<SharedSMTRef> clauses =
        generateSMT(modules, analysisResults, fileOpts);
    // Remove check-sat and get-model
    clauses.pop_back();
    clauses.pop_back();
    if (ImplicationsFlag) {
        // Add the necessary implications
        for (auto invariantIt : invariantCandidates) {
            Mark mark = invariantIt.first;
            if (mark < Mark(0)) {
                continue;
            }
            vector<SortedVar> args;
            vector<smt::SharedSMTRef> stringArgs;

            for (const auto &var : filterVars(1, freeVarsMap.at(mark))) {
                args.push_back(var);
                stringArgs.push_back(smt::stringExpr(var.name));
            }
            if (SMTGenerationOpts::getInstance().Heap) {
                args.push_back(SortedVar("HEAP$1", memoryType()));
                stringArgs.push_back(smt::stringExpr("HEAP$1"));
            }

            for (auto var : filterVars(2, freeVarsMap.at(mark))) {
                args.push_back(var);
                stringArgs.push_back(smt::stringExpr(var.name));
            }
            if (SMTGenerationOpts::getInstance().Heap) {
                args.push_back(SortedVar("HEAP$2", memoryType()));
                stringArgs.push_back(smt::stringExpr("HEAP$2"));
            }
            string invariantName = "INV_MAIN_" + mark.toString();
            string candidateName = invariantName + "_INFERRED";
            SharedSMTRef candidate =
                make_shared<smt::Op>(candidateName, stringArgs);
            SharedSMTRef invariant =
                make_shared<smt::Op>(invariantName, stringArgs);
            SharedSMTRef impl = makeOp("=>", invariant, candidate);
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
cegarDriver(MonoPair<llvm::Module &> modules,
            AnalysisResultsMap &analysisResults,
            vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
            FileOptions fileOpts) {
    auto functions = SMTGenerationOpts::getInstance().MainFunctions;
    const auto markMaps = getBlockMarkMaps(functions, analysisResults);
    MonoPair<BlockNameMap> nameMap = markMaps.map<BlockNameMap>(blockNameMap);
    const auto funArgsPair = getFunctionArguments(functions, analysisResults);
    const auto funArgs = concat(funArgsPair);

    // Run the interpreter on the unrolled code
    MergedAnalysisResults dynamicAnalysisResults;
    MonoPair<PathMap> pathMaps = getPathMaps(functions, analysisResults);
    FreeVarsMap freeVarsMap = getFreeVarsMap(functions, analysisResults);
    size_t degree = DegreeFlag;
    ModelValues vals = initialModelValues(functions);
    auto instrNameMap = instructionNameMap(functions);
    z3::context z3Cxt;
    z3::solver z3Solver(z3Cxt);
    do {
        Mark cexStartMark(
            static_cast<int>(vals.values.at("INV_INDEX_START").get_si()));
        Mark cexEndMark(
            static_cast<int>(vals.values.at("INV_INDEX_END").get_si()));
        // TODO this check needs to include more marks
        if (cexEndMark == EXIT_MARK) {
            std::cerr << "The programs could not be proven equivalent\n";
            exit(1);
        }
        // reconstruct input from counterexample
        auto variableValues = getVarMapFromModel(
            instrNameMap, freeVarsMap.at(cexStartMark), vals.values);

        // dump new example
        std::cout << "---\nFound counterexample:\n";
        std::cout << "at invariant: " << cexStartMark << "\n";
        std::cout << "to invariant: " << cexEndMark << "\n";
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

        assert(markMaps.first.MarkToBlocksMap.at(cexStartMark).size() == 1);
        assert(markMaps.second.MarkToBlocksMap.at(cexStartMark).size() == 1);
        auto firstBlock =
            *markMaps.first.MarkToBlocksMap.at(cexStartMark).begin();
        auto secondBlock =
            *markMaps.second.MarkToBlocksMap.at(cexStartMark).begin();
        std::string tmp;

        MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
            functions, variableValues, getHeapsFromModel(vals.arrays),
            getHeapBackgrounds(vals.arrays), {firstBlock, secondBlock}, 1000);
        // analyzeExecution<const llvm::Value *>(calls, nameMap, debugAnalysis);
        analyzeExecution<const llvm::Value *>(
            calls, nameMap, [&dynamicAnalysisResults, &freeVarsMap, degree,
                             &patterns](MatchInfo<const llvm::Value *> match) {
                ExitIndex exitIndex = getExitIndex(match);
                VarMap<const llvm::Value *> variables(
                    match.steps.first->state.variables);
                variables.insert(match.steps.second->state.variables.begin(),
                                 match.steps.second->state.variables.end());
                findLoopCounts<const llvm::Value *>(
                    dynamicAnalysisResults.loopCounts, match);
                populateEquationsMap(dynamicAnalysisResults.polynomialEquations,
                                     freeVarsMap, match, exitIndex, degree);
                populateHeapPatterns(
                    dynamicAnalysisResults.heapPatternCandidates, patterns,
                    freeVarsMap, match, exitIndex);
            });
        auto loopTransformations = findLoopTransformations(
            dynamicAnalysisResults.loopCounts.loopCounts);
        dumpLoopTransformations(loopTransformations);

        // // Peel and unroll loops
        if (applyLoopTransformation(functions, analysisResults,
                                    loopTransformations, markMaps)) {
            // Reset data and start over
            dynamicAnalysisResults = MergedAnalysisResults();
            vals = initialModelValues(functions);
            // The paths have changed so we need to update the free variables
            pathMaps = getPathMaps(functions, analysisResults);
            freeVarsMap = mergeVectorMaps(
                freeVars(pathMaps.first, funArgsPair.first, Program::First),
                freeVars(pathMaps.second, funArgsPair.second, Program::Second));
            instrNameMap = instructionNameMap(functions);
            std::cerr << "Transformed program, resetting inputs\n";
            continue;
        }

        auto invariantCandidates = makeInvariantDefinitions(
            findSolutions(dynamicAnalysisResults.polynomialEquations),
            dynamicAnalysisResults.heapPatternCandidates, freeVarsMap,
            DegreeFlag);

        SMTGenerationOpts::initialize(
            functions, SMTGenerationOpts::getInstance().Heap, false, false,
            false, false, false, false, false, false, false, true, false, false,
            invariantCandidates, {}, {});
        vector<SharedSMTRef> clauses =
            generateSMT(modules, analysisResults, fileOpts);
        z3Solver.reset();
        std::map<std::string, z3::expr> nameMap;
        std::map<std::string, smt::Z3DefineFun> defineFunMap;
        vector<SharedSMTRef> z3Clauses;
        set<SortedVar> introducedVariables;
        for (const auto &clause : clauses) {
            z3Clauses.push_back(clause->removeForalls(introducedVariables));
        }

        // these variables are not quantified otherwise so we need to add them
        // separately
        VarDecl({"INV_INDEX_START", int64Type()})
            .toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        VarDecl({"INV_INDEX_END", int64Type()})
            .toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        for (const auto &var : introducedVariables) {
            VarDecl(var).toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        }
        for (const auto &clause : z3Clauses) {
            clause->toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        }
        bool unsat = false;
        switch (z3Solver.check()) {
        case z3::unsat:
            std::cout << "Unsat\n";
            unsat = true;
            break;
        case z3::sat:
            std::cout << "Sat\n";
            break;
        case z3::unknown:
            std::cout << "Fuck why is this unknown\n";
            exit(1);
        }
        if (unsat) {
            break;
        }
        z3::model z3Model = z3Solver.get_model();
        vals = parseZ3Model(z3Cxt, z3Model, nameMap, freeVarsMap);
    } while (1 /* sat */);
    std::cerr << "The two programs have been proven equivalent\n";
    auto invariantCandidates = makeInvariantDefinitions(
        findSolutions(dynamicAnalysisResults.polynomialEquations),
        dynamicAnalysisResults.heapPatternCandidates, freeVarsMap, DegreeFlag);

    SMTGenerationOpts::initialize(
        functions, SMTGenerationOpts::getInstance().Heap, false, false, false,
        false, false, false, false, false, false, true, false, false,
        invariantCandidates, {}, {});
    vector<SharedSMTRef> clauses =
        generateSMT(modules, analysisResults, fileOpts);

    return clauses;
}

ModelValues parseZ3Model(const z3::context &z3Cxt, const z3::model &model,
                         const std::map<std::string, z3::expr> &nameMap,
                         const FreeVarsMap &freeVarsMap) {
    ModelValues modelValues;

    Mark startMark =
        Mark(model.eval(nameMap.at("INV_INDEX_START")).get_numeral_int());
    Mark endMark =
        Mark(model.eval(nameMap.at("INV_INDEX_END")).get_numeral_int());
    modelValues.values.insert({"INV_INDEX_START", startMark.asInt()});
    modelValues.values.insert({"INV_INDEX_END", endMark.asInt()});
    for (const auto &var : freeVarsMap.at(startMark)) {
        std::string stringVal = Z3_get_numeral_string(
            z3Cxt, model.eval(nameMap.at(var.name + "_old")));
        modelValues.values.insert({var.name + "_old", mpz_class(stringVal)});
    }
    if (SMTGenerationOpts::getInstance().Heap) {
        auto heap1Eval = model.eval(nameMap.at("HEAP$1_old"));
        auto heap2Eval = model.eval(nameMap.at("HEAP$2_old"));
        modelValues.arrays.insert(
            {"HEAP$1_old", getArrayVal(z3Cxt, heap1Eval)});
        modelValues.arrays.insert(
            {"HEAP$2_old", getArrayVal(z3Cxt, heap2Eval)});
    }
    return modelValues;
}

ArrayVal getArrayVal(const z3::context &z3Cxt, z3::expr arrayExpr) {
    ArrayVal ret;
    while (arrayExpr.decl().decl_kind() == Z3_OP_STORE) {
        ret.vals.insert(
            {mpz_class(Z3_get_numeral_string(z3Cxt, arrayExpr.arg(1))),
             mpz_class(Z3_get_numeral_string(z3Cxt, arrayExpr.arg(2)))});
        arrayExpr = arrayExpr.arg(0);
    }
    if (arrayExpr.decl().decl_kind() != Z3_OP_CONST_ARRAY) {
        logError("Expected constant array\n");
        exit(1);
    }
    ret.background = mpz_class(Z3_get_numeral_string(z3Cxt, arrayExpr.arg(0)));
    return ret;
}

bool applyLoopTransformation(
    MonoPair<llvm::Function *> &functions, AnalysisResultsMap &analysisResults,
    const map<Mark, LoopTransformation> &loopTransformations,
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
                peelAtMark(*functions.first, mapIt.first, marks.first, "1");
                break;
            case LoopTransformSide::Right:
                peelAtMark(*functions.second, mapIt.first, marks.second, "2");
                break;
            }
            break;
        case LoopTransformType::Unroll:
            switch (mapIt.second.side) {
            case LoopTransformSide::Left:
                unrollAtMark(*functions.first, mapIt.first, marks.first,
                             mapIt.second.count);
                break;
            case LoopTransformSide::Right:
                unrollAtMark(*functions.second, mapIt.first, marks.second,
                             mapIt.second.count);
                break;
            }
            break;
        }
    }
    // Update path analysis
    analysisResults.at(functions.first).paths = findPaths(marks.first);
    analysisResults.at(functions.second).paths = findPaths(marks.second);
    return modified;
}

void dumpLoopTransformations(
    map<Mark, LoopTransformation> loopTransformations) {
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

map<Mark, LoopTransformation> findLoopTransformations(LoopCountMap &map) {
    std::map<Mark, int32_t> peelCount;
    std::map<Mark, float> unrollQuotients;
    for (auto mapIt : map) {
        Mark mark = mapIt.first;
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
    std::map<Mark, LoopTransformation> transforms;
    for (auto it : peelCount) {
        Mark mark = it.first;
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
                          FreeVarsMap freeVarsMap,
                          MatchInfo<const llvm::Value *> match,
                          ExitIndex exitIndex, size_t degree) {
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

ExitIndex getExitIndex(const MatchInfo<const llvm::Value *> match) {
    for (auto var : match.steps.first->state.variables) {
        if (var.first->getName() == "exitIndex$1_" + match.mark.toString()) {
            return unsafeIntVal(var.second).asUnbounded();
        }
    }
    for (auto var : match.steps.second->state.variables) {
        if (var.first->getName() == "exitIndex$1_" + match.mark.toString()) {
            return unsafeIntVal(var.second).asUnbounded();
        }
    }
    return 0;
}

void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
    FreeVarsMap freeVarsMap, MatchInfo<const llvm::Value *> match,
    ExitIndex exitIndex) {
    VarMap<const llvm::Value *> variables(match.steps.first->state.variables);
    variables.insert(match.steps.second->state.variables.begin(),
                     match.steps.second->state.variables.end());
    // TODO don’t copy heaps
    MonoPair<Heap> heaps = makeMonoPair(match.steps.first->state.heap,
                                        match.steps.second->state.heap);
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

Optional<MonoPair<llvm::Function *>>
findFunction(const vector<MonoPair<llvm::Function *>> functions,
             string functionName) {
    for (auto &f : functions) {
        if (f.first->getName() == functionName) {
            return Optional<MonoPair<llvm::Function *>>(f);
        }
    }
    return Optional<MonoPair<llvm::Function *>>();
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
        Mark mark = eqMapIt.first;
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
                     const FreeVarsMap &freeVarsMap) {
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
        std::string mulName =
            SMTGenerationOpts::getInstance().BitVect ? "bvmul" : "*";
        if (eq.at(i) > 0) {
            if (eq.at(i) == 1) {
                left.push_back(polynomialTerms.at(i));
            } else {
                left.push_back(makeOp(mulName, smtFromMpz(32, eq.at(i)),
                                      polynomialTerms.at(i)));
            }
        } else if (eq.at(i) < 0) {
            mpz_class inv = -eq.at(i);
            if (inv == 1) {
                right.push_back(polynomialTerms.at(i));
            } else {
                right.push_back(makeOp(mulName, smtFromMpz(32, inv),
                                       polynomialTerms.at(i)));
            }
        }
    }
    if (eq.back() > 0) {
        left.push_back(std::make_unique<ConstantInt>(
            llvm::APInt(32, eq.back().get_str(), 10)));
    } else if (eq.back() < 0) {
        mpz_class inv = -eq.back();
        right.push_back(smtFromMpz(32, inv));
    }
    SharedSMTRef leftSide = nullptr;
    if (left.size() == 0) {
        leftSide = smtFromMpz(32, 0);
    } else if (left.size() == 1) {
        leftSide = left.front();
    } else {
        if (SMTGenerationOpts::getInstance().BitVect) {
            leftSide = make_shared<Op>("bvadd", left);
        } else {
            leftSide = make_shared<Op>("+", left);
        }
    }
    SharedSMTRef rightSide = nullptr;
    if (right.size() == 0) {
        rightSide = smtFromMpz(32, 0);
    } else if (right.size() == 1) {
        rightSide = right.front();
    } else {
        if (SMTGenerationOpts::getInstance().BitVect) {
            rightSide = make_shared<Op>("bvadd", right);
        } else {
            rightSide = make_shared<Op>("+", right);
        }
    }
    return makeOp("=", leftSide, rightSide);
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
        conjunction.push_back(candidate->toSMT());
    }
    if (conjunction.size() == 0) {
        return make_unique<ConstantBool>(false);
    } else {
        return make_shared<Op>("and", conjunction);
    }
}

SharedSMTRef
makeBoundsDefinitions(const map<string, Bound<Optional<VarIntVal>>> &bounds) {
    vector<SharedSMTRef> constraints;
    for (auto mapIt : bounds) {
        if (mapIt.second.lower.hasValue()) {
            constraints.push_back(makeOp(
                "<=", mapIt.second.lower.getValue().get_str(), mapIt.first));
        }
        if (mapIt.second.upper.hasValue()) {
            constraints.push_back(smt::makeOp(
                "<=", mapIt.first, mapIt.second.upper.getValue().get_str()));
        }
    }
    return make_shared<Op>("and", constraints);
}

map<Mark, SharedSMTRef>
makeInvariantDefinitions(const PolynomialSolutions &solutions,
                         const HeapPatternCandidatesMap &patterns,
                         const FreeVarsMap &freeVarsMap, size_t degree) {
    map<Mark, SharedSMTRef> definitions;
    for (auto mapIt : freeVarsMap) {
        Mark mark = mapIt.first;
        vector<SortedVar> args;
        vector<string> stringArgs;
        for (const auto &var : filterVars(1, freeVarsMap.at(mark))) {
            args.push_back(SortedVar(var.name, var.type->copy()));
        }
        if (SMTGenerationOpts::getInstance().Heap) {
            args.push_back(SortedVar("HEAP$1", memoryType()));
        }

        for (auto var : filterVars(2, freeVarsMap.at(mark))) {
            args.push_back(SortedVar(var.name, var.type->copy()));
        }
        if (SMTGenerationOpts::getInstance().Heap) {
            args.push_back(SortedVar("HEAP$2", memoryType()));
        }
        auto solutionsMapIt = solutions.find(mark);
        vector<SharedSMTRef> exitClauses;
        if (solutionsMapIt == solutions.end()) {
            exitClauses.push_back(make_unique<ConstantBool>(false));
        } else {
            for (auto exitIt : solutionsMapIt->second) {
                ExitIndex exit = exitIt.first;
                SharedSMTRef left = makeInvariantDefinition(
                    exitIt.second.left,
                    patterns.at(mark).at(exit).left.hasValue()
                        ? patterns.at(mark).at(exit).left.getValue()
                        : HeapPatternCandidates(),
                    freeVarsMap.at(mark), degree);
                SharedSMTRef right = makeInvariantDefinition(
                    exitIt.second.right,
                    patterns.at(mark).at(exit).right.hasValue()
                        ? patterns.at(mark).at(exit).right.getValue()
                        : HeapPatternCandidates(),
                    freeVarsMap.at(mark), degree);
                SharedSMTRef none = makeInvariantDefinition(
                    exitIt.second.none,
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
                //         makeOp("and", invariant,
                //                   makeBoundsDefinitions(bounds.at(mark)));
                // }
            }
        }
        string invariantName = "INV_MAIN_" + mark.toString();
        if (ImplicationsFlag) {
            invariantName += "_INFERRED";
        }
        definitions[mark] =
            make_shared<FunDef>(invariantName, args, boolType(),
                                make_shared<Op>("or", exitClauses));
    }
    return definitions;
}

void instantiateBounds(map<Mark, map<string, Bound<VarIntVal>>> &boundsMap,
                       const FreeVarsMap &freeVars, MatchInfo<string> match) {
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
    const std::map<Mark, std::map<std::string, Bound<VarIntVal>>> &update) {
    for (auto updateIt : update) {
        Mark mark = updateIt.first;
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

map<Mark, map<ExitIndex, LoopInfoData<set<MonoPair<string>>>>>
extractEqualities(const PolynomialEquations &polynomialEquations,
                  const vector<string> &freeVars) {
    map<Mark, map<ExitIndex, LoopInfoData<set<MonoPair<string>>>>> result;
    for (auto mapIt : polynomialEquations) {
        Mark mark = mapIt.first;
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
        if (SMTGenerationOpts::getInstance().BitVect &&
            arg->getType()->isIntegerTy()) {
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
    if (!SMTGenerationOpts::getInstance().Heap) {
        return {{}, {}};
    }
    return {getHeapFromModel(arrays.at("HEAP$1_old")),
            getHeapFromModel(arrays.at("HEAP$2_old"))};
}

MonoPair<Integer> getHeapBackgrounds(std::map<std::string, ArrayVal> arrays) {
    if (!SMTGenerationOpts::getInstance().Heap) {
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
                if (SMTGenerationOpts::getInstance().BitVect) {
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
        Mark mark = it.first;
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
        Mark mark = it.first;
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
        Mark mark = it.first;
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
    // 5 is chosen because it usually gives us at least a few loop iterationsc
    for (const auto &arg : funs.first->args()) {
        vals.values.insert({std::string(arg.getName()) + "_old", 5});
    }
    for (const auto &arg : funs.second->args()) {
        vals.values.insert({std::string(arg.getName()) + "_old", 5});
    }
    vals.values.insert({"INV_INDEX_START", ENTRY_MARK.asInt()});
    // Anything not negative works here
    vals.values.insert({"INV_INDEX_END", 0});
    return vals;
}
