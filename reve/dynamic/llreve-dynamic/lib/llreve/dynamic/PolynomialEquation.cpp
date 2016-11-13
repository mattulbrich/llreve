#include "llreve/dynamic/PolynomialEquation.h"

#include "llreve/dynamic/Util.h"

using std::vector;
using std::string;

using smt::int64Type;
using smt::SortedVar;

namespace llreve {
namespace dynamic {
void populateEquationsMap(
    IterativeInvariantMap<PolynomialEquations> &polynomialEquations,
    vector<smt::SortedVar> primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex, size_t degree) {
    VarMap<string> variables;
    for (auto varIt : match.steps.first->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    for (auto varIt : match.steps.second->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    vector<mpq_class> equation;
    for (size_t i = 1; i <= degree; ++i) {
        auto polynomialTerms = polynomialTermsOfDegree(primitiveVariables, i);
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
            .insert(make_pair(exitIndex,
                              LoopInfoData<Matrix<mpq_class>>({}, {}, {})));
        getDataForLoopInfo(polynomialEquations.at(match.mark).at(exitIndex),
                           match.loopInfo) = {equation};
    } else {
        Matrix<mpq_class> vecs = getDataForLoopInfo(
            polynomialEquations.at(match.mark).at(exitIndex), match.loopInfo);
        vecs.push_back(equation);
        if (!linearlyIndependent(vecs)) {
            return;
        }
        getDataForLoopInfo(polynomialEquations.at(match.mark).at(exitIndex),
                           match.loopInfo)
            .push_back(equation);
    }
}

void populateEquationsMap(
    RelationalFunctionInvariantMap<
        LoopInfoData<FunctionInvariant<Matrix<mpq_class>>>> &equationsMap,
    vector<SortedVar> primitiveVariables,
    CoupledCallInfo<const llvm::Value *> match, size_t degree) {
    auto &polynomialEquations = equationsMap[match.functions];
    VarMap<string> variables;
    for (auto varIt : match.steps.first->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    for (auto varIt : match.steps.second->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    variables.insert({resultName(Program::First), match.returnValues.first});
    variables.insert({resultName(Program::Second), match.returnValues.second});
    vector<smt::SortedVar> preVariables = primitiveVariables;
    vector<smt::SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(Program::First), int64Type());
    postVariables.emplace_back(resultName(Program::Second), int64Type());
    vector<mpq_class> preEquation;
    vector<mpq_class> postEquation;
    for (size_t i = 1; i <= degree; ++i) {
        auto prePolynomialTerms = polynomialTermsOfDegree(preVariables, i);
        auto postPolynomialTerms = polynomialTermsOfDegree(postVariables, i);
        for (auto term : prePolynomialTerms) {
            mpz_class termVal = 1;
            for (auto var : term) {
                termVal *= unsafeIntVal(variables.at(var)).asUnbounded();
            }
            preEquation.push_back(termVal);
        }
        for (auto term : postPolynomialTerms) {
            mpz_class termVal = 1;
            for (auto var : term) {
                termVal *= unsafeIntVal(variables.at(var)).asUnbounded();
            }
            postEquation.push_back(termVal);
        }
    }
    // Add a constant at the end of each vector
    preEquation.push_back(1);
    postEquation.push_back(1);
    if (polynomialEquations.count(match.mark) == 0) {
        polynomialEquations.insert(
            {match.mark, {{{}, {}}, {{}, {}}, {{}, {}}}});
        getDataForLoopInfo(polynomialEquations.at(match.mark),
                           match.loopInfo) = {{preEquation}, {postEquation}};
    } else {
        auto &vecsRef = getDataForLoopInfo(polynomialEquations.at(match.mark),
                                           match.loopInfo);
        auto preVecs = vecsRef.preCondition;
        auto postVecs = vecsRef.postCondition;
        preVecs.push_back(preEquation);
        postVecs.push_back(postEquation);
        if (linearlyIndependent(preVecs)) {
            vecsRef.preCondition = preVecs;
        }
        if (linearlyIndependent(postVecs)) {
            vecsRef.postCondition = postVecs;
        }
    }
}

void populateEquationsMap(FunctionInvariantMap<Matrix<mpq_class>> &equationsMap,
                          vector<SortedVar> primitiveVariables,
                          UncoupledCallInfo<const llvm::Value *> match,
                          size_t degree) {
    auto &polynomialEquations = equationsMap[match.function];
    VarMap<string> variables;
    for (auto varIt : match.step->state.variables) {
        variables.insert(std::make_pair(varIt.first->getName(), varIt.second));
    }
    variables.insert({resultName(match.prog), match.returnValue});
    vector<smt::SortedVar> preVariables = primitiveVariables;
    vector<smt::SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(match.prog), int64Type());
    vector<mpq_class> preEquation;
    vector<mpq_class> postEquation;
    for (size_t i = 1; i <= degree; ++i) {
        auto prePolynomialTerms = polynomialTermsOfDegree(preVariables, i);
        auto postPolynomialTerms = polynomialTermsOfDegree(postVariables, i);
        for (auto term : prePolynomialTerms) {
            mpz_class termVal = 1;
            for (auto var : term) {
                termVal *= unsafeIntVal(variables.at(var)).asUnbounded();
            }
            preEquation.push_back(termVal);
        }
        for (auto term : postPolynomialTerms) {
            mpz_class termVal = 1;
            for (auto var : term) {
                termVal *= unsafeIntVal(variables.at(var)).asUnbounded();
            }
            postEquation.push_back(termVal);
        }
    }
    // Add a constant at the end of each vector
    preEquation.push_back(1);
    postEquation.push_back(1);
    auto polynomialEquationsIt = polynomialEquations.find(match.mark);
    if (polynomialEquationsIt == polynomialEquations.end()) {
        polynomialEquations.insert(
            {match.mark, {{preEquation}, {postEquation}}});
    } else {
        auto &equationsForMark = polynomialEquationsIt->second;
        auto preVecs = equationsForMark.preCondition;
        auto postVecs = equationsForMark.postCondition;
        preVecs.push_back(preEquation);
        postVecs.push_back(postEquation);
        if (linearlyIndependent(preVecs)) {
            equationsForMark.preCondition = preVecs;
        }
        if (linearlyIndependent(postVecs)) {
            equationsForMark.postCondition = postVecs;
        }
    }
}
}
}
