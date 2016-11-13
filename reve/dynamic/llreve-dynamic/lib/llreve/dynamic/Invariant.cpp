#include "llreve/dynamic/Invariant.h"

#include "Invariant.h"
#include "llreve/dynamic/Interpreter.h"
#include "llreve/dynamic/Linear.h"
#include "llreve/dynamic/Util.h"

using std::map;
using std::vector;
using std::string;
using std::make_unique;
using std::make_shared;
using std::multiset;

using llvm::Optional;

using namespace smt;
using namespace llreve::opts;

namespace llreve {
namespace dynamic {

static std::unique_ptr<ConstantInt> smtFromMpz(unsigned bitWidth, mpz_class i) {
    return std::make_unique<ConstantInt>(
        llvm::APInt(bitWidth, i.get_str(), 10));
}

map<Mark, SharedSMTRef> makeIterativeInvariantDefinitions(
    MonoPair<const llvm::Function *> functions,
    const IterativeInvariantMap<PolynomialEquations> &equations,
    const HeapPatternCandidatesMap &patterns,
    const AnalysisResultsMap &analysisResults, size_t degree) {
    const auto solutions = findSolutions(equations);
    map<Mark, SharedSMTRef> definitions;
    for (auto mapIt : analysisResults.at(functions.first).freeVariables) {
        Mark mark = mapIt.first;
        vector<SortedVar> args;
        for (const auto &var :
             analysisResults.at(functions.first).freeVariables.at(mark)) {
            args.push_back(var);
        }
        for (const auto &var :
             analysisResults.at(functions.second).freeVariables.at(mark)) {
            args.push_back(var);
        }
        auto solutionsMapIt = solutions.find(mark);
        vector<SharedSMTRef> exitClauses;
        if (solutionsMapIt == solutions.end()) {
            exitClauses.push_back(make_unique<ConstantBool>(false));
        } else {
            for (auto exitIt : solutionsMapIt->second) {
                ExitIndex exit = exitIt.first;
                const auto freeVariables =
                    getFreeVariablesForMark(functions, mark, analysisResults);
                SharedSMTRef left = makeInvariantDefinition(
                    exitIt.second.left,
                    patterns.at(mark).at(exit).left.hasValue()
                        ? patterns.at(mark).at(exit).left.getValue()
                        : HeapPatternCandidates(),
                    freeVariables, degree);
                SharedSMTRef right = makeInvariantDefinition(
                    exitIt.second.right,
                    patterns.at(mark).at(exit).right.hasValue()
                        ? patterns.at(mark).at(exit).right.getValue()
                        : HeapPatternCandidates(),
                    freeVariables, degree);
                SharedSMTRef none = makeInvariantDefinition(
                    exitIt.second.none,
                    patterns.at(mark).at(exit).none.hasValue()
                        ? patterns.at(mark).at(exit).none.getValue()
                        : HeapPatternCandidates(),
                    freeVariables, degree);
                if (left == nullptr && right == nullptr && none == nullptr) {
                    continue;
                }
                vector<SharedSMTRef> invariantDisjunction;
                if (left != nullptr) {
                    invariantDisjunction.push_back(left);
                }
                if (right != nullptr) {
                    invariantDisjunction.push_back(right);
                }
                if (none != nullptr) {
                    invariantDisjunction.push_back(none);
                }
                SharedSMTRef invariant =
                    make_shared<Op>("or", invariantDisjunction);
                exitClauses.push_back(invariant);
            }
        }
        string invariantName = "INV_MAIN_" + mark.toString();
        if (ImplicationsFlag) {
            invariantName += "_INFERRED";
        }
        SMTRef body;
        if (exitClauses.empty()) {
            body = make_unique<ConstantBool>(true);
        } else {
            body = make_unique<Op>("or", exitClauses);
        }
        definitions[mark] = make_shared<FunDef>(invariantName, args, boolType(),
                                                std::move(body));
    }
    return definitions;
}

RelationalFunctionInvariantMap<FunctionInvariant<smt::SharedSMTRef>>
makeRelationalFunctionInvariantDefinitions(
    const RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>> &equations,
    const AnalysisResultsMap &analysisResults, size_t degree) {
    RelationalFunctionInvariantMap<FunctionInvariant<smt::SharedSMTRef>>
        definitions;
    for (const auto &coupledFunctions :
         SMTGenerationOpts::getInstance().CoupledFunctions) {
        // Taking the intersection of the freevars maps would be the correct
        // thing to do here but defining too many functions does no harm and
        // intersecting maps is a pain in the ass in c++
        for (const auto mapIt :
             analysisResults.at(coupledFunctions.first).freeVariables) {
            const AnalysisResults &analysisResults1 =
                analysisResults.at(coupledFunctions.first);
            const AnalysisResults &analysisResults2 =
                analysisResults.at(coupledFunctions.second);
            Mark mark = mapIt.first;
            if (!mark.hasInvariant()) {
                continue;
            }
            vector<SortedVar> invariantArgsPost;
            vector<SortedVar> invariantArgsPre;
            invariantArgsPost.insert(
                invariantArgsPost.end(),
                analysisResults1.freeVariables.at(mark).begin(),
                analysisResults1.freeVariables.at(mark).end());
            invariantArgsPost.insert(
                invariantArgsPost.end(),
                analysisResults2.freeVariables.at(mark).begin(),
                analysisResults2.freeVariables.at(mark).end());
            invariantArgsPre = invariantArgsPost;
            invariantArgsPost.push_back(
                {resultName(Program::First), int64Type()});
            invariantArgsPost.push_back(
                {resultName(Program::Second), int64Type()});
            string preName = invariantName(mark, ProgramSelection::Both,
                                           getFunctionName(coupledFunctions),
                                           InvariantAttr::PRE);
            string postName = invariantName(mark, ProgramSelection::Both,
                                            getFunctionName(coupledFunctions));
            SharedSMTRef preInvBody = make_unique<ConstantBool>(false);
            SharedSMTRef postInvBody = make_unique<ConstantBool>(false);
            auto equationsIt = equations.find(coupledFunctions);
            if (equationsIt != equations.end()) {
                auto markIt = equationsIt->second.find(mark);
                if (markIt != equationsIt->second.end()) {
                    preInvBody = makeInvariantDefinition(
                        findSolutions(markIt->second.none.preCondition), {},
                        invariantArgsPre, degree);
                    if (preInvBody == nullptr) {
                        preInvBody = make_unique<ConstantBool>(true);
                    }
                    postInvBody = makeInvariantDefinition(
                        findSolutions(markIt->second.none.postCondition), {},
                        invariantArgsPost, degree);
                    if (postInvBody == nullptr) {
                        postInvBody = make_unique<ConstantBool>(true);
                    }
                }
            }
            auto preInv = make_shared<FunDef>(preName, invariantArgsPre,
                                              boolType(), preInvBody);
            auto postInv = make_shared<FunDef>(postName, invariantArgsPost,
                                               boolType(), postInvBody);
            definitions[coupledFunctions].insert({mark, {preInv, postInv}});
        }
    }
    return definitions;
}

FunctionInvariantMap<smt::SharedSMTRef> makeFunctionInvariantDefinitions(
    MonoPair<const llvm::Module &> modules,
    const FunctionInvariantMap<Matrix<mpq_class>> &equations,
    const AnalysisResultsMap &analysisResults, size_t degree) {
    auto invariants = makeFunctionInvariantDefinitions(
        modules.first, equations, analysisResults, Program::First, degree);
    auto invariants2 = makeFunctionInvariantDefinitions(
        modules.second, equations, analysisResults, Program::Second, degree);
    invariants.insert(invariants2.begin(), invariants2.end());
    return invariants;
}

FunctionInvariantMap<smt::SharedSMTRef> makeFunctionInvariantDefinitions(
    const llvm::Module &module,
    const FunctionInvariantMap<Matrix<mpq_class>> &equations,
    const AnalysisResultsMap &analysisResults, Program prog, size_t degree) {
    FunctionInvariantMap<smt::SharedSMTRef> definitions;
    for (const auto &function : module) {
        if (hasFixedAbstraction(function)) {
            continue;
        }
        for (const auto mapIt : analysisResults.at(&function).freeVariables) {
            const Mark mark = mapIt.first;
            if (!mark.hasInvariant()) {
                continue;
            }
            vector<SortedVar> invariantArgsPost;
            vector<SortedVar> invariantArgsPre;
            invariantArgsPost.insert(invariantArgsPost.end(),
                                     mapIt.second.begin(), mapIt.second.end());
            invariantArgsPre = invariantArgsPost;
            invariantArgsPost.push_back({resultName(prog), int64Type()});
            string preName =
                invariantName(mark, asSelection(prog), function.getName(),
                              InvariantAttr::PRE);
            string postName =
                invariantName(mark, asSelection(prog), function.getName());
            SharedSMTRef preCondition = make_unique<ConstantBool>(false);
            SharedSMTRef postCondition = make_unique<ConstantBool>(false);
            nestedLookup(equations, &function, mark,
                         [&](auto mapIt) {
                             preCondition = makeInvariantDefinition(
                                 findSolutions(mapIt->second.preCondition), {},
                                 invariantArgsPre, degree);
                             postCondition = makeInvariantDefinition(
                                 findSolutions(mapIt->second.postCondition), {},
                                 invariantArgsPost, degree);
                         },
                         [] {});
            auto preConditionDef = make_unique<FunDef>(
                preName, invariantArgsPre, boolType(), preCondition);
            auto postConditionDef = make_unique<FunDef>(
                postName, invariantArgsPost, boolType(), postCondition);
            definitions[&function].insert(
                {mark,
                 {std::move(preConditionDef), std::move(postConditionDef)}});
        }
    }
    return definitions;
}

SharedSMTRef
makeBoundsDefinitions(const map<string, Bound<Optional<VarIntVal>>> &bounds) {
    vector<SharedSMTRef> constraints;
    for (auto mapIt : bounds) {
        if (mapIt.second.lower.hasValue()) {
            constraints.push_back(makeOp(
                "<=",
                smtFromMpz(64, mapIt.second.lower.getValue().asUnbounded()),
                mapIt.first));
        }
        if (mapIt.second.upper.hasValue()) {
            constraints.push_back(smt::makeOp(
                "<=", mapIt.first,
                smtFromMpz(64, mapIt.second.upper.getValue().asUnbounded())));
        }
    }
    return make_shared<Op>("and", constraints);
}

SharedSMTRef makeInvariantDefinition(const vector<vector<mpz_class>> &solution,
                                     const HeapPatternCandidates &candidates,
                                     const vector<SortedVar> &freeVars,
                                     size_t degree) {
    vector<SharedSMTRef> conjunction;
    auto primitiveVariables = removeHeapVariables(freeVars);
    for (const auto &vec : solution) {
        conjunction.push_back(makeEquation(vec, primitiveVariables, degree));
    }
    for (const auto &candidate : candidates) {
        conjunction.push_back(candidate->toSMT());
    }
    if (conjunction.size() == 0) {
        return nullptr;
    } else {
        return make_shared<Op>("and", conjunction);
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
        left.push_back(smtFromMpz(64, eq.back()));
    } else if (eq.back() < 0) {
        right.push_back(smtFromMpz(64, -eq.back()));
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

Matrix<mpz_class> findSolutions(Matrix<mpq_class> equations) {
    Matrix<mpq_class> solution = nullSpace(equations);
    Matrix<mpz_class> integerSolution(solution.size());
    for (size_t i = 0; i < solution.size(); ++i) {
        integerSolution.at(i) = ratToInt(solution.at(i));
    }
    return integerSolution;
}
PolynomialSolutions findSolutions(
    const IterativeInvariantMap<PolynomialEquations> &polynomialEquations) {
    PolynomialSolutions map;
    for (auto eqMapIt : polynomialEquations) {
        Mark mark = eqMapIt.first;
        for (auto exitMapIt : eqMapIt.second) {
            ExitIndex exitIndex = exitMapIt.first;
            LoopInfoData<Matrix<mpz_class>> n = {
                findSolutions(exitMapIt.second.left),
                findSolutions(exitMapIt.second.right),
                findSolutions(exitMapIt.second.none)};
            map[mark].insert(make_pair(exitMapIt.first, n));
        }
    }
    return map;
}
}
}
