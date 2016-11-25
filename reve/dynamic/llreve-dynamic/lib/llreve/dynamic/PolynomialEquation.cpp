#include "llreve/dynamic/PolynomialEquation.h"

#include "llreve/dynamic/Util.h"

using std::vector;
using std::string;

using smt::int64Type;
using smt::SortedVar;

namespace llreve {
namespace dynamic {

static mpz_class evalTerm(const std::vector<std::string> &term,
                          const VarMap<string> &variables) {
    mpz_class termVal = 1;
    for (const auto &var : term) {
        termVal *= variables.find(var)->second.asUnbounded();
    }
    return termVal;
}

static vector<mpq_class>
createEquation(const vector<SortedVar> &primitiveVariables,
               const VarMap<string> &variables, unsigned maxDegree) {
    vector<mpq_class> equation;
    for (size_t i = 1; i <= maxDegree; ++i) {
        auto polynomialTerms = polynomialTermsOfDegree(primitiveVariables, i);
        for (const auto &term : polynomialTerms) {
            equation.push_back(evalTerm(term, variables));
        }
    }
    // this represents the constant
    equation.push_back(1);
    return equation;
}

static void insertInStringMap(const FastVarMap &variables,
                              VarMap<string> &stringVariables) {
    for (auto varIt : variables) {
        stringVariables.insert({varIt.first->getName(), varIt.second});
    }
}

static VarMap<string> getStringVarMap(const FastVarMap &variables) {
    VarMap<string> stringVariables;
    insertInStringMap(variables, stringVariables);
    return stringVariables;
}

static VarMap<string> getStringVarMap(const FastVarMap &variables1,
                                      const FastVarMap &variables2) {
    VarMap<string> stringVariables;
    insertInStringMap(variables1, stringVariables);
    insertInStringMap(variables2, stringVariables);
    return stringVariables;
}

void populateEquationsMap(
    IterativeInvariantMap<PolynomialEquations> &polynomialEquations,
    const vector<smt::SortedVar> &primitiveVariables,
    MatchInfo<const llvm::Value *> match, ExitIndex exitIndex, size_t degree) {
    VarMap<string> variables =
        getStringVarMap(match.steps.first->state.variables,
                        match.steps.second->state.variables);
    vector<mpq_class> equation =
        createEquation(primitiveVariables, variables, degree);
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
    const vector<SortedVar> &primitiveVariables,
    CoupledCallInfo<const llvm::Value *> match, size_t degree) {
    auto &polynomialEquations = equationsMap[match.functions];
    VarMap<string> variables =
        getStringVarMap(match.steps.first->state.variables,
                        match.steps.second->state.variables);
    variables.insert({resultName(Program::First), match.returnValues.first});
    variables.insert({resultName(Program::Second), match.returnValues.second});
    vector<smt::SortedVar> preVariables = primitiveVariables;
    vector<smt::SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(Program::First), int64Type());
    postVariables.emplace_back(resultName(Program::Second), int64Type());
    vector<mpq_class> preEquation =
        createEquation(preVariables, variables, degree);
    vector<mpq_class> postEquation =
        createEquation(postVariables, variables, degree);
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
                          const vector<SortedVar> &primitiveVariables,
                          UncoupledCallInfo<const llvm::Value *> match,
                          size_t degree) {
    auto &polynomialEquations = equationsMap[match.function];
    VarMap<string> variables = getStringVarMap(match.step->state.variables);
    variables.insert({resultName(match.prog), match.returnValue});
    vector<smt::SortedVar> preVariables = primitiveVariables;
    vector<smt::SortedVar> postVariables = preVariables;
    postVariables.emplace_back(resultName(match.prog), int64Type());
    vector<mpq_class> preEquation =
        createEquation(preVariables, variables, degree);
    vector<mpq_class> postEquation =
        createEquation(postVariables, variables, degree);
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
