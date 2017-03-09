#include "Declaration.h"

#include "FreeVariables.h"
#include "Helper.h"
#include "Invariant.h"

using smt::SharedSMTRef;
using smt::SMTRef;
using std::string;
using std::vector;

using namespace llreve::opts;

vector<SharedSMTRef>
relationalFunctionDeclarations(MonoPair<const llvm::Function *> functions,
                               const AnalysisResultsMap &analysisResults) {
    const string functionName = getFunctionName(functions);
    const auto pathMaps = getPathMaps(functions, analysisResults);
    // TODO Do we need to take the intersection of the pathmaps here?
    const auto pathMap = pathMaps.first;
    const auto returnType = functions.first->getReturnType();
    const auto functionArguments =
        getFunctionArguments(functions, analysisResults);
    const auto freeVarsMap = getFreeVarsMap(functions, analysisResults);
    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        const auto &fixedInvariants =
            SMTGenerationOpts::getInstance().FunctionalRelationalInvariants;
        nestedLookup(fixedInvariants, functions, startIndex,
                     [&declarations](auto it) {
                         declarations.push_back(it->second.preCondition);
                         declarations.push_back(it->second.postCondition);
                     },
                     [&declarations, startIndex, &freeVarsMap, functionName,
                      &returnType]() {
                         MonoPair<SMTRef> invariants = invariantDeclaration(
                             startIndex, freeVarsMap.at(startIndex),
                             ProgramSelection::Both, functionName, returnType);
                         declarations.push_back(std::move(invariants.first));
                         declarations.push_back(std::move(invariants.second));
                     });
    }
    return declarations;
}

vector<SharedSMTRef>
functionalFunctionDeclarations(const llvm::Function *function,
                               const AnalysisResultsMap &analysisResults,
                               Program prog) {
    const string functionName = function->getName().str();
    const auto pathMap = analysisResults.at(function).paths;
    const auto returnType = function->getReturnType();
    const auto functionArguments =
        analysisResults.at(function).functionArguments;
    const auto freeVarsMap = analysisResults.at(function).freeVariables;

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        const auto &fixedInvariants =
            SMTGenerationOpts::getInstance().FunctionalFunctionalInvariants;
        nestedLookup(fixedInvariants, function, startIndex,
                     [&declarations](auto it) {
                         declarations.push_back(it->second.preCondition);
                         declarations.push_back(it->second.postCondition);
                     },
                     [startIndex, prog, functionName, &returnType, &freeVarsMap,
                      &declarations]() {
                         MonoPair<SMTRef> invariants = invariantDeclaration(
                             startIndex, freeVarsMap.at(startIndex),
                             asSelection(prog), functionName, returnType);
                         declarations.push_back(std::move(invariants.first));
                         declarations.push_back(std::move(invariants.second));
                     });
    }
    return declarations;
}
vector<SharedSMTRef> relationalIterativeDeclarations(
    MonoPair<const llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults) {
    const auto pathMaps = getPathMaps(preprocessedFunctions, analysisResults);
    // TODO Do we need to take the intersection of the pathmaps here?
    const auto pathMap = pathMaps.first;
    const string functionName = getFunctionName(preprocessedFunctions);
    const auto functionArguments =
        getFunctionArguments(preprocessedFunctions, analysisResults);
    const auto freeVarsMap =
        getFreeVarsMap(preprocessedFunctions, analysisResults);

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        if (startIndex != ENTRY_MARK) {
            // ignore entry node, it has the fixed predicate IN_INV
            auto foundIt = SMTGenerationOpts::getInstance()
                               .IterativeRelationalInvariants.find(startIndex);
            if (foundIt ==
                SMTGenerationOpts::getInstance()
                    .IterativeRelationalInvariants.end()) {
                auto invariant = mainInvariantDeclaration(
                    startIndex, freeVarsMap.at(startIndex),
                    ProgramSelection::Both, functionName);
                declarations.push_back(
                    mainInvariantComment(startIndex, freeVarsMap.at(startIndex),
                                         ProgramSelection::Both, functionName));
                declarations.push_back(std::move(invariant));
            } else {
                declarations.push_back(foundIt->second);
            }
        }
    }
    return declarations;
}
