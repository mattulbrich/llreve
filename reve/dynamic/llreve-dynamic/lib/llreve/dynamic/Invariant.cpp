#include "llreve/dynamic/Invariant.h"

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
    const IterativeInvariantMap<PolynomialEquations> &equations,
    const HeapPatternCandidatesMap &patterns, const FreeVarsMap &freeVarsMap,
    size_t degree) {
    const auto solutions = findSolutions(equations);
    map<Mark, SharedSMTRef> definitions;
    for (auto mapIt : freeVarsMap) {
        Mark mark = mapIt.first;
        vector<SortedVar> args;
        vector<string> stringArgs;
        for (const auto &var : filterVars(1, freeVarsMap.at(mark))) {
            args.push_back(var);
        }
        for (auto var : filterVars(2, freeVarsMap.at(mark))) {
            args.push_back(var);
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
        return make_unique<ConstantBool>(false);
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

PolynomialSolutions findSolutions(
    const IterativeInvariantMap<PolynomialEquations> &polynomialEquations) {
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
}
}
