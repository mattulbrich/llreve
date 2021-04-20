/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "llreve/dynamic/Analysis.h"

#include "Compat.h"
#include "MarkAnalysis.h"
#include "ModuleSMTGeneration.h"
#include "MonoPair.h"
#include "PathAnalysis.h"
#include "Serialize.h"
#include "llreve/dynamic/HeapPattern.h"
#include "llreve/dynamic/Interpreter.h"
#include "llreve/dynamic/Linear.h"
#include "llreve/dynamic/Peel.h"
#include "llreve/dynamic/PolynomialEquation.h"
#include "llreve/dynamic/SerializeTraces.h"
#include "llreve/dynamic/Unroll.h"
#include "llreve/dynamic/Util.h"

#include <fstream>
#include <iostream>
#include <random>
#include <regex>
#include <thread>

// I don't care about windows
#include <dirent.h>
#include <stdio.h>
#include <sys/stat.h>

#include "llvm/IR/Verifier.h"

using llvm::Module;
using llvm::Optional;

using std::ifstream;
using std::ios;
using std::list;
using std::make_shared;
using std::make_unique;
using std::map;
using std::multiset;
using std::set;
using std::shared_ptr;
using std::static_pointer_cast;
using std::string;
using std::vector;

using namespace smt;
using namespace std::placeholders;
using namespace llreve::opts;

namespace llreve {
namespace dynamic {

static llreve::cl::opt<bool>
    PrettyFlag("pretty", llreve::cl::desc("Pretty print intermediate output"));
static llreve::cl::opt<unsigned>
    DegreeFlag("degree",
               llreve::cl::desc("Degree of the polynomial invariants"),
               llreve::cl::init(1));
static llreve::cl::opt<bool, true> ImplicationsFlagStorage(
    "implications",
    llreve::cl::desc("Add implications instead of replacing invariants"),
    llvm::cl::location(ImplicationsFlag));
static llreve::cl::opt<bool>
    StepFlag("step",
             llreve::cl::desc(
                 "Pause after each counterexample until return is pressed"));
static llreve::cl::opt<bool> DumpIntermediateSMTFlag(
    "intermediate-smt",
    llreve::cl::desc("Dump intermediate SMT files for debugginr purposes"));
// 10 seems to perform pretty well in the benchmarks I tried
static llreve::cl::opt<unsigned> InterpretStepsFlag(
    "interpret-steps",
    llreve::cl::desc(
        "The number of instructions that are interpreted for each example"),
    cl::init(10));

bool ImplicationsFlag;

static void wait() {
    if (StepFlag) {
        string line;
        std::getline(std::cin, line);
    }
}

Transformed analyzeMainCounterExample(
    MarkPair pathMarks, ModelValues &vals, MonoPair<llvm::Function *> functions,
    DynamicAnalysisResults &dynamicAnalysisResults,
    AnalysisResultsMap &analysisResults,
    llvm::StringMap<const llvm::Value *> &instrNameMap,
    const MonoPair<BlockNameMap> &nameMap,
    const vector<shared_ptr<HeapPattern<VariablePlaceholder>>> &patterns,
    unsigned degree) {
    const auto markMaps = getBlockMarkMaps(functions, analysisResults);
    // reconstruct input from counterexample
    auto variableValues = getVarMapFromModel(
        instrNameMap,
        {getPrimitiveFreeVariables(functions.first, pathMarks.startMark,
                                   analysisResults),
         getPrimitiveFreeVariables(functions.second, pathMarks.startMark,
                                   analysisResults)},
        vals.values);

    dumpCounterExample(pathMarks.startMark, pathMarks.endMark, variableValues,
                       vals.arrays);

    wait();

    assert(markMaps.first.MarkToBlocksMap.at(pathMarks.startMark).size() == 1);
    assert(markMaps.second.MarkToBlocksMap.at(pathMarks.startMark).size() == 1);
    auto firstBlock =
        *markMaps.first.MarkToBlocksMap.at(pathMarks.startMark).begin();
    auto secondBlock =
        *markMaps.second.MarkToBlocksMap.at(pathMarks.startMark).begin();

    MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
        functions, variableValues, getHeapsFromModel(vals.arrays),
        {firstBlock, secondBlock}, InterpretStepsFlag, analysisResults);
    analyzeExecution<const llvm::Value *>(
        std::move(calls), nameMap, analysisResults,
        [&](MatchInfo<const llvm::Value *> match) {
            ExitIndex exitIndex = getExitIndex(match);
            findLoopCounts<const llvm::Value *>(
                dynamicAnalysisResults.loopCounts, match);
            const auto primitiveVariables = getPrimitiveFreeVariables(
                functions, match.mark, analysisResults);
            populateEquationsMap(dynamicAnalysisResults.polynomialEquations,
                                 primitiveVariables, match, exitIndex, degree);
            populateHeapPatterns(dynamicAnalysisResults.heapPatternCandidates,
                                 patterns, primitiveVariables, match,
                                 exitIndex);
        },
        [&](CoupledCallInfo<const llvm::Value *> match) {
            const auto primitiveVariables = getPrimitiveFreeVariables(
                match.functions, match.mark, analysisResults);
            auto returnInstrs =
                getReturnInstructions(match.functions, analysisResults);
            populateEquationsMap(
                dynamicAnalysisResults.relationalFunctionPolynomialEquations,
                primitiveVariables, match, degree);
            populateHeapPatterns(
                dynamicAnalysisResults.relationalFunctionHeapPatterns, patterns,
                primitiveVariables, match, returnInstrs);
        },
        [&](UncoupledCallInfo<const llvm::Value *> match) {
            const auto primitiveVariables = getPrimitiveFreeVariables(
                match.function, match.mark, analysisResults);
            populateEquationsMap(
                dynamicAnalysisResults.functionPolynomialEquations,
                primitiveVariables, match, degree);
            populateHeapPatterns(
                dynamicAnalysisResults.functionHeapPatterns, patterns,
                primitiveVariables, match,
                analysisResults.at(match.function).returnInstruction);

        });
    auto loopTransformations =
        findLoopTransformations(dynamicAnalysisResults.loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);

    // // Peel and unroll loops
    if (applyLoopTransformation(functions, analysisResults, loopTransformations,
                                markMaps)) {
        // Reset data and start over
        dynamicAnalysisResults = DynamicAnalysisResults();
        vals = initialModelValues(functions);
        // The paths have changed so we need to update the free variables
        analysisResults.at(functions.first).freeVariables =
            freeVars(analysisResults.at(functions.first).paths,
                     analysisResults.at(functions.first).functionArguments,
                     Program::First);
        analysisResults.at(functions.second).freeVariables =
            freeVars(analysisResults.at(functions.second).paths,
                     analysisResults.at(functions.second).functionArguments,
                     Program::Second);
        instrNameMap = instructionNameMap(functions);
        std::cerr << "Transformed program, resetting inputs\n";
        return Transformed::Yes;
    }
    return Transformed::No;
}

void analyzeRelationalCounterExample(
    MarkPair pathMarks, const ModelValues &vals,
    MonoPair<const llvm::Function *> functions,
    DynamicAnalysisResults &dynamicAnalysisResults,
    const MonoPair<BlockNameMap> &nameMap,
    const AnalysisResultsMap &analysisResults, unsigned maxDegree) {
    const auto markMaps = getBlockMarkMaps(functions, analysisResults);
    auto primitiveFreeVariables = getPrimitiveFreeVariables(
        functions, pathMarks.startMark, analysisResults);
    // reconstruct input from counterexample
    // TODO we could cache the result of instructionNameMap somewhere
    auto variableValues = getVarMapFromModel(
        instructionNameMap(functions),
        {getPrimitiveFreeVariables(functions.first, pathMarks.startMark,
                                   analysisResults),
         getPrimitiveFreeVariables(functions.second, pathMarks.startMark,
                                   analysisResults)},

        vals.values);

    dumpCounterExample(pathMarks.startMark, pathMarks.endMark, variableValues,
                       vals.arrays);

    wait();

    assert(markMaps.first.MarkToBlocksMap.at(pathMarks.startMark).size() == 1);
    assert(markMaps.second.MarkToBlocksMap.at(pathMarks.startMark).size() == 1);
    auto firstBlock =
        *markMaps.first.MarkToBlocksMap.at(pathMarks.startMark).begin();
    auto secondBlock =
        *markMaps.second.MarkToBlocksMap.at(pathMarks.startMark).begin();

    MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
        functions, variableValues, getHeapsFromModel(vals.arrays),
        {firstBlock, secondBlock}, InterpretStepsFlag, analysisResults);
    analyzeCoupledCalls<const llvm::Value *>(
        calls.first, calls.second, nameMap, analysisResults,
        [&](CoupledCallInfo<const llvm::Value *> match) {
            const auto primitiveVariables = getPrimitiveFreeVariables(
                match.functions, match.mark, analysisResults);
            populateEquationsMap(
                dynamicAnalysisResults.relationalFunctionPolynomialEquations,
                primitiveVariables, match, maxDegree);
        },
        [&](UncoupledCallInfo<const llvm::Value *> match) {
            populateEquationsMap(
                dynamicAnalysisResults.functionPolynomialEquations,
                removeHeapVariables(analysisResults.at(match.function)
                                        .freeVariables.at(match.mark)),
                match, maxDegree);
        });
}

void analyzeFunctionalCounterExample(
    MarkPair pathMarks, const ModelValues &vals, const llvm::Function *function,
    Program program, DynamicAnalysisResults &dynamicAnalysisResults,
    const BlockNameMap &blockNameMap, const AnalysisResultsMap &analysisResults,
    unsigned maxDegree) {
    const auto markMap = analysisResults.at(function).blockMarkMap;
    auto primitiveFreeVariables = getPrimitiveFreeVariables(
        function, pathMarks.startMark, analysisResults);
    // reconstruct input from counterexample
    // TODO we could cache the result of instructionNameMap somewhere
    auto variableValues =
        getVarMapFromModel(instructionNameMap(function),
                           getPrimitiveFreeVariables(
                               function, pathMarks.startMark, analysisResults),
                           vals.values);

    dumpCounterExample(pathMarks.startMark, pathMarks.endMark, variableValues,
                       vals.arrays);

    wait();

    assert(markMap.MarkToBlocksMap.at(pathMarks.startMark).size() == 1);
    auto startBlock = *markMap.MarkToBlocksMap.at(pathMarks.startMark).begin();

    Call<const llvm::Value *> call = interpretFunction(
        *function,
        FastState(variableValues, getHeapFromModel(vals.arrays, program)),
        startBlock, InterpretStepsFlag, analysisResults);
    std::cout << "analyzing trace\n";
    analyzeUncoupledCall<const llvm::Value *>(
        call, blockNameMap, program, analysisResults,
        [&](UncoupledCallInfo<const llvm::Value *> match) {
            populateEquationsMap(
                dynamicAnalysisResults.functionPolynomialEquations,
                removeHeapVariables(analysisResults.at(match.function)
                                        .freeVariables.at(match.mark)),
                match, maxDegree);
        });
    std::cout << "analyzed trace\n";
}

static llvm::SmallDenseMap<HeapAddress, Integer>
randomHeap(const llvm::Function &fun, const FastVarMap &variableValues,
           int lengthBound, int valLowerBound, int valUpperBound,
           unsigned int *seedp) {
    // We place an array with a random length <= lengthBound with random values
    // >= valLowerBound and <= valUpperBound at each pointer argument
    llvm::SmallDenseMap<HeapAddress, Integer> heap;
    for (const auto &arg : fun.args()) {
        if (arg.getType()->isPointerTy()) {
            Integer arrayStart = variableValues.find(&arg)->second;
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
static void analyzeExample(
    std::function<void(MonoPair<Call<const llvm::Value *>>)> callback,
    MonoPair<std::vector<mpz_class>> initialValues,
    MonoPair<const llvm::Function *> funs,
    AnalysisResultsMap &analysisResults) {
    unsigned int seedp = static_cast<unsigned int>(time(NULL));
    MonoPair<FastVarMap> variableValues = {FastVarMap(), FastVarMap()};
    variableValues.first = getVarMap(funs.first, initialValues.first);
    variableValues.second = getVarMap(funs.second, initialValues.second);
    auto heap =
        randomHeap(*funs.first, variableValues.first, 5, -20, 20, &seedp);
    MonoPair<Heap> heaps = {{heap, Integer(0)}, {heap, Integer(0)}};
    MonoPair<Call<const llvm::Value *>> calls = interpretFunctionPair(
        funs, std::move(variableValues), heaps, 10000, analysisResults);
    callback(std::move(calls));
}

static unsigned randomExamples = 50;
static void iterateTracesInRange(
    MonoPair<llvm::Function *> funs, mpz_class lowerBound, mpz_class upperBound,
    AnalysisResultsMap &analysisResults,
    std::function<void(MonoPair<Call<const llvm::Value *>>)> callback) {
    assert(!(funs.first->isVarArg() || funs.second->isVarArg()));
    std::vector<Integer> argValues;

    assert(funs.first->arg_size() == funs.second->arg_size());
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_int_distribution<> distribution(0, 100);
    for (unsigned i = 0; i < randomExamples; ++i) {
        std::vector<mpz_class> vals(funs.first->arg_size());
        for (auto &val : vals) {
            val = mpz_class(distribution(gen));
        }
        for (auto val : vals) {
            std::cout << val << ", ";
        }
        std::cout << "\n";
        analyzeExample(callback, {vals, vals}, funs, analysisResults);
    }
}

vector<SharedSMTRef>
driver(MonoPair<llvm::Module &> modules, AnalysisResultsMap &analysisResults,
       vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
       FileOptions fileOpts) {
    auto functionPair = SMTGenerationOpts::getInstance().MainFunctions;
    const MonoPair<BidirBlockMarkMap> markMaps =
        getBlockMarkMaps(functionPair, analysisResults);
    MonoPair<BlockNameMap> nameMap = getBlockNameMaps(analysisResults);
    const auto funArgsPair =
        getFunctionArguments(functionPair, analysisResults);
    std::vector<SortedVar> funArgs;
    funArgs.insert(funArgs.end(), funArgsPair.first.begin(),
                   // MU bugfix? funArgsPair.second.end());
                   funArgsPair.first.end());
    funArgs.insert(funArgs.end(), funArgsPair.second.begin(),
                   funArgsPair.second.end());

    // Collect loop info
    LoopCountsAndMark loopCounts;
    iterateTracesInRange(functionPair, 47, 50, analysisResults,
                         [&](MonoPair<Call<const llvm::Value *>> calls) {
                             analyzeExecution<const llvm::Value *>(
                                 std::move(calls), nameMap, analysisResults,
                                 [&](MatchInfo<const llvm::Value *> matchInfo) {
                                     findLoopCounts<const llvm::Value *>(
                                         loopCounts, matchInfo);
                                 },
                                 // We ignore functions for now
                                 [](auto match) {}, [](auto match) {});
                         });
    auto loopTransformations = findLoopTransformations(loopCounts.loopCounts);
    dumpLoopTransformations(loopTransformations);

    // Peel and unroll loops
    applyLoopTransformation(functionPair, analysisResults, loopTransformations,
                            markMaps);
    analysisResults.at(functionPair.first).freeVariables =
        freeVars(analysisResults.at(functionPair.first).paths,
                 analysisResults.at(functionPair.first).functionArguments,
                 Program::First);
    analysisResults.at(functionPair.second).freeVariables =
        freeVars(analysisResults.at(functionPair.second).paths,
                 analysisResults.at(functionPair.second).functionArguments,
                 Program::Second);

    return generateSMT(modules, analysisResults, fileOpts);
}

std::vector<smt::SharedSMTRef>
cegarDriver(MonoPair<llvm::Module &> modules,
            AnalysisResultsMap &analysisResults,
            vector<shared_ptr<HeapPattern<VariablePlaceholder>>> patterns,
            FileOptions fileOpts) {
    auto functions = SMTGenerationOpts::getInstance().MainFunctions;
    MonoPair<BlockNameMap> blockNameMap = getBlockNameMaps(analysisResults);

    // Run the interpreter on the unrolled code
    DynamicAnalysisResults dynamicAnalysisResults;
    size_t degree = DegreeFlag;
    ModelValues vals = initialModelValues(functions);
    auto instrNameMap = instructionNameMap(functions);
    z3::context z3Cxt;
    z3::solver z3Solver(z3Cxt);
    // We start by assuming equivalence and change it to non equivalence
    LlreveResult result = LlreveResult::Equivalent;
    do {
        Mark cexStartMark(
            static_cast<int>(vals.values.at("INV_INDEX_START").get_si()));
        Mark cexEndMark(
            static_cast<int>(vals.values.at("INV_INDEX_END").get_si()));
        std::cout << "MAIN: " << vals.main << "\n";
        std::cout << "startMark: " << cexStartMark << "\n";
        std::cout << "endMark: " << cexEndMark << "\n";
        if (vals.functions.first) {
            std::cout << "function 1: " << vals.functions.first->getName().str()
                      << "\n";
        }
        if (vals.functions.second) {
            std::cout << "function 2: "
                      << vals.functions.second->getName().str() << "\n";
        }
        // TODO we can’t stop if there is a function call on this path so for
        // now we disable this
        // if ((vals.main && cexEndMark == EXIT_MARK) ||
        //     cexEndMark == FORBIDDEN_MARK) {
        //     // There are two cases in which no invariant refinement is
        //     possible:
        //     // we can’t refine the fixed exit relation and we can’t refine
        //     // anything if the programs diverge
        //     result = LlreveResult::NotEquivalent;
        //     break;
        // }

        assert(vals.functions.first || vals.functions.second);
        if (vals.main) {
            Transformed transformed = analyzeMainCounterExample(
                {cexStartMark, cexEndMark}, vals, functions,
                dynamicAnalysisResults, analysisResults, instrNameMap,
                blockNameMap, patterns, degree);
            if (transformed == Transformed::Yes) {
                continue;
            }
        } else if (vals.functions.first && vals.functions.second) {
            analyzeRelationalCounterExample(
                {cexStartMark, cexEndMark}, vals, vals.functions,
                dynamicAnalysisResults, blockNameMap, analysisResults, degree);
        } else if (vals.functions.first) {
            analyzeFunctionalCounterExample(
                {cexStartMark, cexEndMark}, vals, vals.functions.first,
                Program::First, dynamicAnalysisResults, blockNameMap.first,
                analysisResults, degree);
        } else if (vals.functions.second) {
            analyzeFunctionalCounterExample(
                {cexStartMark, cexEndMark}, vals, vals.functions.second,
                Program::Second, dynamicAnalysisResults, blockNameMap.second,
                analysisResults, degree);
        }

        auto invariantCandidates = makeIterativeInvariantDefinitions(
            functions, dynamicAnalysisResults.polynomialEquations,
            dynamicAnalysisResults.heapPatternCandidates, analysisResults,
            DegreeFlag);
        auto relationalFunctionInvariantCandidates =
            makeRelationalFunctionInvariantDefinitions(
                dynamicAnalysisResults.relationalFunctionPolynomialEquations,
                dynamicAnalysisResults.relationalFunctionHeapPatterns,
                analysisResults, DegreeFlag);
        auto functionInvariantCandidates = makeFunctionInvariantDefinitions(
            modules, dynamicAnalysisResults.functionPolynomialEquations,
            dynamicAnalysisResults.functionHeapPatterns, analysisResults,
            DegreeFlag);

        SMTGenerationOpts::getInstance().IterativeRelationalInvariants =
            invariantCandidates;
        SMTGenerationOpts::getInstance().FunctionalRelationalInvariants =
            relationalFunctionInvariantCandidates;
        SMTGenerationOpts::getInstance().FunctionalFunctionalInvariants =
            functionInvariantCandidates;
        vector<SharedSMTRef> clauses =
            generateSMT(modules, analysisResults, fileOpts);
        z3Solver.reset();
        llvm::StringMap<z3::expr> nameMap;
        llvm::StringMap<smt::Z3DefineFun> defineFunMap;
        vector<SharedSMTRef> z3Clauses;
        set<SortedVar> introducedVariables;
        for (const auto &clause : clauses) {
            z3Clauses.push_back(removeForalls(*clause, introducedVariables));
        }
        vector<SharedSMTRef> introducedClauses;
        for (const auto &var : introducedVariables) {
            introducedClauses.push_back(make_unique<VarDecl>(var));
            VarDecl(var).toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        }
        z3Clauses.insert(z3Clauses.begin(), introducedClauses.begin(),
                         introducedClauses.end());
        for (const auto &clause : z3Clauses) {
            clause->toZ3(z3Cxt, z3Solver, nameMap, defineFunMap);
        }
        if (DumpIntermediateSMTFlag) {
            serializeSMT(z3Clauses, false,
                         SerializeOpts("out.smt2", true, false, true, false));
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
            std::cout << "Why is this unknown :(\n";
            exit(1);
        }
        if (unsat) {
            break;
        }
        z3::model z3Model = z3Solver.get_model();
        vals = parseZ3Model(z3Cxt, z3Model, nameMap, analysisResults);
    } while (1 /* sat */);

    vector<SharedSMTRef> clauses;
    switch (result) {
    case LlreveResult::Equivalent: {
        std::cerr << "The programs have been proven equivalent\n";
        auto invariantCandidates = makeIterativeInvariantDefinitions(
            functions, dynamicAnalysisResults.polynomialEquations,
            dynamicAnalysisResults.heapPatternCandidates, analysisResults,
            DegreeFlag);
        auto relationalFunctionInvariantCandidates =
            makeRelationalFunctionInvariantDefinitions(
                dynamicAnalysisResults.relationalFunctionPolynomialEquations,
                dynamicAnalysisResults.relationalFunctionHeapPatterns,
                analysisResults, DegreeFlag);
        auto functionInvariantCandidates = makeFunctionInvariantDefinitions(
            modules, dynamicAnalysisResults.functionPolynomialEquations,
            dynamicAnalysisResults.functionHeapPatterns, analysisResults,
            DegreeFlag);

        SMTGenerationOpts::getInstance().IterativeRelationalInvariants =
            invariantCandidates;
        SMTGenerationOpts::getInstance().FunctionalRelationalInvariants =
            relationalFunctionInvariantCandidates;
        SMTGenerationOpts::getInstance().FunctionalFunctionalInvariants =
            functionInvariantCandidates;
        clauses = generateSMT(modules, analysisResults, fileOpts);
        break;
    }
    case LlreveResult::NotEquivalent: {
        std::cerr << "The programs could not be proved equivalent\n";
        clauses = {};
        break;
    }
    }
    return clauses;
}

static ProgramSelection toSelection(bool program1, bool program2) {
    if (program1 && program2) {
        return ProgramSelection::Both;
    }
    if (program1 && !program2) {
        return ProgramSelection::First;
    }
    if (!program1 && program2) {
        return ProgramSelection::Second;
    }
    logError("Inverted smt output is invalid\n");
    exit(1);
}

// Z3_lbool can be implicitely casted to a boolean but the result is useless, so
// always use this explicit conversion
static bool convertZ3Bool(Z3_lbool val) {
    switch (val) {
    case Z3_L_TRUE:
        return true;
    case Z3_L_FALSE:
        return false;
    case Z3_L_UNDEF:
        logError("Cannot handle Z3 undef value\n");
        exit(1);
    }
}

ModelValues parseZ3Model(const z3::context &z3Cxt, const z3::model &model,
                         const llvm::StringMap<z3::expr> &nameMap,
                         const AnalysisResultsMap &analysisResults) {
    map<string, ArrayVal> arrays;
    map<string, mpz_class> values;

    Mark startMark = Mark(
        model.eval(nameMap.find("INV_INDEX_START")->second).get_numeral_int());
    Mark endMark = Mark(
        model.eval(nameMap.find("INV_INDEX_END")->second).get_numeral_int());
    values.insert({"INV_INDEX_START", startMark.asInt()});
    values.insert({"INV_INDEX_END", endMark.asInt()});
    bool main = convertZ3Bool(
        Z3_get_bool_value(z3Cxt, model.eval(nameMap.find("MAIN")->second)));
    bool program1 = convertZ3Bool(Z3_get_bool_value(
        z3Cxt, model.eval(nameMap.find("PROGRAM_1")->second)));
    bool program2 = convertZ3Bool(Z3_get_bool_value(
        z3Cxt, model.eval(nameMap.find("PROGRAM_2")->second)));
    const llvm::Function *function1 = nullptr;
    const llvm::Function *function2 = nullptr;
    if (program1) {
        function1 =
            SMTGenerationOpts::getInstance().ReversedFunctionNumerals.first.at(
                model.eval(nameMap.find("FUNCTION_1")->second)
                    .get_numeral_int64());
        for (const auto &var :
             getPrimitiveFreeVariables(function1, startMark, analysisResults)) {
            std::string stringVal = Z3_get_numeral_string(
                z3Cxt, model.eval(nameMap.find(var.name + "_old")->second));
            values.insert({var.name + "_old", mpz_class(stringVal)});
        }
    }
    if (program2) {
        function2 =
            SMTGenerationOpts::getInstance().ReversedFunctionNumerals.second.at(
                model.eval(nameMap.find("FUNCTION_2")->second)
                    .get_numeral_int64());
        for (const auto &var :
             getPrimitiveFreeVariables(function2, startMark, analysisResults)) {
            std::string stringVal = Z3_get_numeral_string(
                z3Cxt, model.eval(nameMap.find(var.name + "_old")->second));
            values.insert({var.name + "_old", mpz_class(stringVal)});
        }
    }
    if (SMTGenerationOpts::getInstance().Heap ==
        llreve::opts::HeapOpt::Enabled) {
        if (program1) {
            auto heap1Eval = model.eval(nameMap.find("HEAP$1_old")->second);
            arrays.insert({"HEAP$1_old", getArrayVal(z3Cxt, heap1Eval)});
        }
        if (program2) {
            auto heap2Eval = model.eval(nameMap.find("HEAP$2_old")->second);
            arrays.insert({"HEAP$2_old", getArrayVal(z3Cxt, heap2Eval)});
        }
    }

    return ModelValues(arrays, values, main, toSelection(program1, program2),
                       {function1, function2});
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
            // TODO we need to mark things as modified here
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
    std::cerr << "-----\nLoop transformations\n";
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
    std::cerr << "-----\n";
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
                factor < 1 ? LoopTransformSide::Right : LoopTransformSide::Left;
            factor = factor < 1 ? 1 / factor : factor;
            transforms.insert(std::make_pair(
                mark,
                LoopTransformation(LoopTransformType::Unroll, side,
                                   static_cast<size_t>(std::round(factor)))));
        }
    }
    return transforms;
}

ExitIndex getExitIndex(const MatchInfo<const llvm::Value *> match) {
    for (auto var : match.steps.first->state.variables) {
        if (var.first->getName() == "exitIndex$1_" + match.mark.toString()) {
            return var.second.asUnbounded();
        }
    }
    for (auto var : match.steps.second->state.variables) {
        if (var.first->getName() == "exitIndex$1_" + match.mark.toString()) {
            return var.second.asUnbounded();
        }
    }
    return 0;
}

static void filterPatterns(HeapPatternCandidates &patterns,
                           const FastVarMap &variables,
                           MonoPair<const Heap &> heaps) {
    auto listIt = patterns.begin();
    while (listIt != patterns.end()) {
        if (!(*listIt)->matches(variables, heaps)) {
            listIt = patterns.erase(listIt);
        } else {
            ++listIt;
        }
    }
}

void populateHeapPatterns(
    HeapPatternCandidatesMap &heapPatternCandidates,
    const vector<shared_ptr<HeapPattern<VariablePlaceholder>>> &patterns,
    const vector<SortedVar> &primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex) {
    VarMap<const llvm::Value *> variables(match.steps.first->state.variables);
    variables.insert(match.steps.second->state.variables.begin(),
                     match.steps.second->state.variables.end());
    // TODO don’t copy heaps
    MonoPair<const Heap &> heaps(match.steps.first->state.heap,
                                 match.steps.second->state.heap);
    bool newCandidates =
        heapPatternCandidates[match.mark].count(exitIndex) == 0 ||
        !getDataForLoopInfo(heapPatternCandidates.at(match.mark).at(exitIndex),
                            match.loopInfo)
             .hasValue();
    if (newCandidates) {
        list<shared_ptr<HeapPattern<const llvm::Value *>>> candidates;
        for (auto pat : patterns) {
            auto newCandidates =
                pat->instantiate(primitiveVariables, variables, heaps);
            candidates.splice(candidates.end(), newCandidates);
        }
        // This entry could already be present
        auto it = heapPatternCandidates.at(match.mark)
                      .insert({exitIndex,
                               {Optional<HeapPatternCandidates>(),
                                Optional<HeapPatternCandidates>(),
                                Optional<HeapPatternCandidates>()}});
        auto &patternCandidates =
            getDataForLoopInfo(it.first->second, match.loopInfo);
        assert(!patternCandidates.hasValue());
        patternCandidates = std::move(candidates);
    } else {
        HeapPatternCandidates &patterns =
            getDataForLoopInfo(
                heapPatternCandidates.at(match.mark).at(exitIndex),
                match.loopInfo)
                .getValue();
        filterPatterns(patterns, variables, heaps);
    }
}

void populateHeapPatterns(
    RelationalFunctionInvariantMap<
        LoopInfoData<llvm::Optional<FunctionInvariant<HeapPatternCandidates>>>>
        &heapPatternCandidates,
    const vector<shared_ptr<HeapPattern<VariablePlaceholder>>> &patterns,
    const vector<SortedVar> &primitiveVariables,
    CoupledCallInfo<const llvm::Value *> match,
    MonoPair<llvm::Value *> returnValues) {
    VarMap<const llvm::Value *> variables(match.steps.first->state.variables);
    variables.insert(match.steps.second->state.variables.begin(),
                     match.steps.second->state.variables.end());
    variables.insert({returnValues.first, match.returnValues.first});
    variables.insert({returnValues.second, match.returnValues.second});
    vector<SortedVar> preVariables = primitiveVariables;
    vector<SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(Program::First), int64Type());
    postVariables.emplace_back(resultName(Program::Second), int64Type());
    // TODO don’t copy heaps
    MonoPair<Heap> heaps = makeMonoPair(match.steps.first->state.heap,
                                        match.steps.second->state.heap);
    bool newCandidates =
        heapPatternCandidates[match.functions].count(match.mark) == 0 ||
        !getDataForLoopInfo(
             heapPatternCandidates.at(match.functions).at(match.mark),
             match.loopInfo)
             .hasValue();
    if (newCandidates) {
        list<shared_ptr<HeapPattern<const llvm::Value *>>> preCandidates;
        list<shared_ptr<HeapPattern<const llvm::Value *>>> postCandidates;
        for (const auto &pat : patterns) {
            auto newCandidates =
                pat->instantiate(preVariables, variables, heaps);
            preCandidates.splice(preCandidates.end(), newCandidates);
            newCandidates =
                pat->instantiate(postVariables, variables, heaps, returnValues);
            postCandidates.splice(postCandidates.end(), newCandidates);
        }
        // This entry could already be present but insert will not do anything
        // in that case
        llvm::Optional<FunctionInvariant<HeapPatternCandidates>> emptyInvariant;
        auto it =
            heapPatternCandidates.at(match.functions)
                .insert({match.mark,
                         {emptyInvariant, emptyInvariant, emptyInvariant}});
        auto &patternCandidates =
            getDataForLoopInfo(it.first->second, match.loopInfo);
        assert(!patternCandidates.hasValue());
        patternCandidates = {std::move(preCandidates),
                             std::move(postCandidates)};
    } else {
        FunctionInvariant<HeapPatternCandidates> &patterns =
            getDataForLoopInfo(
                heapPatternCandidates.at(match.functions).at(match.mark),
                match.loopInfo)
                .getValue();
        filterPatterns(patterns.preCondition, variables, heaps);
        filterPatterns(patterns.postCondition, variables, heaps);
    }
}

void populateHeapPatterns(
    FunctionInvariantMap<HeapPatternCandidates> &heapPatternCandidates,
    const vector<shared_ptr<HeapPattern<VariablePlaceholder>>> &patterns,
    const vector<SortedVar> &primitiveVariables,
    UncoupledCallInfo<const llvm::Value *> match, llvm::Value *returnValue) {
    VarMap<const llvm::Value *> variables(match.step->state.variables);
    variables.insert({returnValue, match.returnValue});
    vector<SortedVar> preVariables = primitiveVariables;
    vector<SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(match.prog), int64Type());
    MonoPair<Heap> heaps = {Heap(), Heap()};
    if (match.prog == Program::First) {
        heaps = {match.step->state.heap, {}};
    } else {
        heaps = {{}, match.step->state.heap};
    }
    bool newCandidates =
        heapPatternCandidates[match.function].count(match.mark) == 0;
    if (newCandidates) {
        list<shared_ptr<HeapPattern<const llvm::Value *>>> preCandidates;
        list<shared_ptr<HeapPattern<const llvm::Value *>>> postCandidates;
        MonoPair<llvm::Value *> returnInstructions(nullptr, nullptr);
        if (match.prog == Program::First) {
            returnInstructions.first = returnValue;
        } else {
            returnInstructions.second = returnValue;
        }
        for (auto pat : patterns) {
            auto newCandidates = pat->instantiate(primitiveVariables, variables,
                                                  heaps, returnInstructions);
            preCandidates.splice(preCandidates.end(), newCandidates);
            newCandidates = pat->instantiate(primitiveVariables, variables,
                                             heaps, returnInstructions);
            postCandidates.splice(postCandidates.end(), newCandidates);
        }
        // TODO figure out postcondition
        heapPatternCandidates.at(match.function)
            .insert({match.mark,
                     {std::move(preCandidates), std::move(postCandidates)}});
    } else {
        FunctionInvariant<HeapPatternCandidates> &patterns =
            heapPatternCandidates.at(match.function).at(match.mark);
        filterPatterns(patterns.preCondition, variables, heaps);
        filterPatterns(patterns.postCondition, variables, heaps);
    }
}

void insertInBlockNameMap(BlockNameMap &nameMap,
                          const BidirBlockMarkMap &blockMap) {
    for (auto it : blockMap.BlockToMarksMap) {
        llvm::SmallVector<Mark, 2> marks(it.second.begin(), it.second.end());
        nameMap[it.first->getName()] = std::move(marks);
    }
}

MonoPair<BlockNameMap>
getBlockNameMaps(const AnalysisResultsMap &analysisResults) {
    BlockNameMap first;
    BlockNameMap second;
    for (const auto &funPair :
         SMTGenerationOpts::getInstance().CoupledFunctions) {
        insertInBlockNameMap(first,
                             analysisResults.at(funPair.first).blockMarkMap);
        insertInBlockNameMap(second,
                             analysisResults.at(funPair.second).blockMarkMap);
    }
    return {first, second};
}

bool normalMarkBlock(const BlockNameMap &map, const BlockName &blockName) {
    auto it = map.find(blockName);
    if (it == map.end()) {
        return false;
    }
    return !std::binary_search(it->second.begin(), it->second.end(),
                               ENTRY_MARK);
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
    std::cerr << match.steps.first
                     ->toJSON([](auto x) -> std::string {
                         return x->getName().str();
                     })
                     .dump(4)
              << std::endl;
    std::cerr << "Second state:" << std::endl;
    std::cerr << match.steps.second
                     ->toJSON(
                         [](auto x) -> std::string { return x->getName(); })
                     .dump(4)
              << std::endl;
    std::cerr << std::endl << std::endl;
}

void dumpPolynomials(
    const IterativeInvariantMap<PolynomialEquations> &equationsMap,
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

FastVarMap getVarMap(const llvm::Function *fun, std::vector<mpz_class> vals) {
    FastVarMap variableValues;
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

llvm::StringMap<const llvm::Value *>
instructionNameMap(const llvm::Function *fun) {
    llvm::StringMap<const llvm::Value *> nameMap;
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

llvm::StringMap<const llvm::Value *>
instructionNameMap(MonoPair<const llvm::Function *> funs) {
    llvm::StringMap<const llvm::Value *> nameMap =
        instructionNameMap(funs.first);
    llvm::StringMap<const llvm::Value *> nameMap2 =
        instructionNameMap(funs.second);
    for (auto &it : nameMap2) {
        nameMap[it.getKey()] = it.getValue();
    }
    return nameMap;
}

MonoPair<FastVarMap> getVarMapFromModel(
    const llvm::StringMap<const llvm::Value *> &instructionNameMap,
    MonoPair<std::vector<smt::SortedVar>> freeVars,
    const std::map<std::string, mpz_class> &vals) {
    return {getVarMapFromModel(instructionNameMap, freeVars.first, vals),
            getVarMapFromModel(instructionNameMap, freeVars.second, vals)};
}

FastVarMap getVarMapFromModel(
    const llvm::StringMap<const llvm::Value *> &instructionNameMap,
    std::vector<smt::SortedVar> freeVars,
    const std::map<std::string, mpz_class> &vals) {
    FastVarMap variableValues(freeVars.size());
    for (const auto &var : freeVars) {
        mpz_class val = vals.at(var.name + "_old");
        const llvm::Value *instr = instructionNameMap.find(var.name)->second;
        variableValues.insert({instr, Integer(val)});
    }
    return variableValues;
}

llvm::SmallDenseMap<HeapAddress, Integer> getHeapFromModel(const ArrayVal &ar) {
    llvm::SmallDenseMap<HeapAddress, Integer> result;
    for (const auto &it : ar.vals) {
        result.insert({Integer(it.first), Integer(it.second)});
    }
    return result;
}

Heap getHeapFromModel(const std::map<std::string, ArrayVal> &arrays,
                      Program prog) {
    if (SMTGenerationOpts::getInstance().Heap ==
        llreve::opts::HeapOpt::Disabled) {
        return {llvm::SmallDenseMap<HeapAddress, Integer>(),
                Integer(mpz_class(0))};
    }
    std::string heap = heapName(prog) + "_old";
    return {getHeapFromModel(arrays.at(heap)),
            Integer(arrays.at(heap).background)};
}

MonoPair<Heap>
getHeapsFromModel(const std::map<std::string, ArrayVal> &arrays) {
    return {getHeapFromModel(arrays, Program::First),
            getHeapFromModel(arrays, Program::Second)};
}

ModelValues initialModelValues(MonoPair<const llvm::Function *> funs) {
    map<string, ArrayVal> arrays;
    map<string, mpz_class> values;
    arrays.insert({"HEAP$1_old", {0, {}}});
    arrays.insert({"HEAP$2_old", {0, {}}});
    // 5 is chosen because it usually gives us at least a few loop iterationsc
    for (const auto &arg : funs.first->args()) {
        values.insert({std::string(arg.getName()) + "_old", 5});
    }
    for (const auto &arg : funs.second->args()) {
        values.insert({std::string(arg.getName()) + "_old", 5});
    }
    values.insert({"INV_INDEX_START", ENTRY_MARK.asInt()});
    // Anything not negative works here
    values.insert({"INV_INDEX_END", 0});
    return ModelValues(arrays, values, true, ProgramSelection::Both, funs);
}

static void dumpVarMap(const FastVarMap &variableValues) {
    for (auto it : variableValues) {
        llvm::errs() << it.first->getName() << " "
                     << it.second.asUnbounded().get_str() << "\n";
    }
}

static void dumpArrays(const map<string, ArrayVal> &arrays) {
    for (auto ar : arrays) {
        std::cout << ar.first << "\n";
        std::cout << "background: " << ar.second.background << "\n";
        for (auto val : ar.second.vals) {
            std::cout << val.first << ":" << val.second << "\n";
        }
    }
}

void dumpCounterExample(Mark cexStartMark, Mark cexEndMark,
                        const MonoPair<FastVarMap> &variableValues,
                        const map<string, ArrayVal> &arrays) {
    std::cout << "---\nFound counterexample:\n";
    std::cout << "starting at mark " << cexStartMark << "\n";
    std::cout << "ending at mark " << cexEndMark << "\n";

    // dump new example
    dumpVarMap(variableValues.first);
    dumpVarMap(variableValues.second);

    dumpArrays(arrays);
}

void dumpCounterExample(Mark cexStartMark, Mark cexEndMark,
                        const FastVarMap &variableValues,
                        const map<string, ArrayVal> &arrays) {
    std::cout << "---\nFound counterexample:\n";
    std::cout << "starting at mark " << cexStartMark << "\n";
    std::cout << "ending at mark " << cexEndMark << "\n";

    // dump new example
    dumpVarMap(variableValues);

    dumpArrays(arrays);
}
} // namespace dynamic
} // namespace llreve
