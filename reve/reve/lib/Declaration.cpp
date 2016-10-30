#include "Declaration.h"

#include "FreeVariables.h"
#include "Helper.h"
#include "Invariant.h"

using smt::SharedSMTRef;
using smt::SMTRef;
using std::string;
using std::vector;

using namespace llreve::opts;

vector<SharedSMTRef> relationalFunctionDeclarations(
    MonoPair<const llvm::Function *> preprocessedFunctions,
    const AnalysisResultsMap &analysisResults) {
    const string functionName = getFunctionName(preprocessedFunctions);
    const auto pathMaps = getPathMaps(preprocessedFunctions, analysisResults);
    // TODO Do we need to take the intersection of the pathmaps here?
    const auto pathMap = pathMaps.first;
    const auto returnType = preprocessedFunctions.first->getReturnType();
    const auto functionArguments =
        getFunctionArguments(preprocessedFunctions, analysisResults);
    const auto freeVarsMap =
        getFreeVarsMap(preprocessedFunctions, analysisResults);

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        MonoPair<SMTRef> invariants = invariantDeclaration(
            startIndex, freeVarsMap.at(startIndex), ProgramSelection::Both,
            functionName, returnType);
        declarations.push_back(std::move(invariants.first));
        declarations.push_back(std::move(invariants.second));
    }
    return declarations;
}

vector<SharedSMTRef>
functionalFunctionDeclarations(const llvm::Function *preprocessedFunction,
                               const AnalysisResultsMap &analysisResults,
                               Program prog) {
    const string functionName = preprocessedFunction->getName().str();
    const auto pathMap = analysisResults.at(preprocessedFunction).paths;
    const auto returnType = preprocessedFunction->getReturnType();
    const auto functionArguments =
        analysisResults.at(preprocessedFunction).functionArguments;
    const auto freeVarsMap =
        analysisResults.at(preprocessedFunction).freeVariables;

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const Mark startIndex = pathMapIt.first;
        MonoPair<SMTRef> invariants =
            invariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                 asSelection(prog), functionName, returnType);
        declarations.push_back(std::move(invariants.first));
        declarations.push_back(std::move(invariants.second));
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
            if (SMTGenerationOpts::getInstance().Invariants.find(startIndex) ==
                SMTGenerationOpts::getInstance().Invariants.end()) {
                const auto invariant = mainInvariantDeclaration(
                    startIndex, freeVarsMap.at(startIndex),
                    ProgramSelection::Both, functionName);
                declarations.push_back(invariant);
            } else {
                declarations.push_back(
                    SMTGenerationOpts::getInstance().Invariants.at(startIndex));
            }
        }
    }
    return declarations;
}
