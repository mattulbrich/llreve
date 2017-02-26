#include "llreve/dynamic/Util.h"

#include "llreve/dynamic/Permutation.h"

#include "CommandLine.h"

using std::vector;
using std::string;

using namespace smt;

namespace llreve {
namespace dynamic {

static llreve::cl::opt<bool>
    MultinomialsFlag("multinomials", llreve::cl::desc("Use true multinomials"));

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

vector<SortedVar> removeHeapVariables(const vector<SortedVar> &freeVariables) {
    vector<SortedVar> result;
    for (const auto &var : freeVariables) {
        if (!isArray(var.type)) {
            result.push_back(var);
        }
    }
    return result;
}

std::vector<smt::SortedVar>
getFreeVariablesForMark(MonoPair<const llvm::Function *> functions, Mark mark,
                        const AnalysisResultsMap &analysisResults) {
    auto primitiveFreeVariables =
        analysisResults.at(functions.first).freeVariables.at(mark);
    auto primitiveFreeVariables2 =
        analysisResults.at(functions.second).freeVariables.at(mark);
    primitiveFreeVariables.insert(primitiveFreeVariables.end(),
                                  primitiveFreeVariables2.begin(),
                                  primitiveFreeVariables2.end());
    return primitiveFreeVariables;
}
std::vector<smt::SortedVar>
getPrimitiveFreeVariables(MonoPair<const llvm::Function *> functions, Mark mark,
                          const AnalysisResultsMap &analysisResults) {
    auto primitiveFreeVariables = removeHeapVariables(
        analysisResults.at(functions.first).freeVariables.at(mark));
    auto primitiveFreeVariables2 = removeHeapVariables(
        analysisResults.at(functions.second).freeVariables.at(mark));
    primitiveFreeVariables.insert(primitiveFreeVariables.end(),
                                  primitiveFreeVariables2.begin(),
                                  primitiveFreeVariables2.end());
    return primitiveFreeVariables;
}

std::vector<smt::SortedVar>
getPrimitiveFreeVariables(const llvm::Function *function, Mark mark,
                          const AnalysisResultsMap &analysisResults) {
    return removeHeapVariables(
        analysisResults.at(function).freeVariables.at(mark));
}
}
}
