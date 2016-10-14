#include "Declaration.h"

#include "FreeVariables.h"
#include "Helper.h"
#include "Invariant.h"

using smt::SharedSMTRef;
using smt::SMTRef;
using std::string;
using std::vector;

vector<SharedSMTRef> relationalFunctionDeclarations(
    MonoPair<PreprocessedFunction> preprocessedFunctions) {
    const string functionName =
        preprocessedFunctions.first.fun->getName().str() + "^" +
        preprocessedFunctions.second.fun->getName().str();
    const auto pathMaps = preprocessedFunctions.map<PathMap>(
        [](PreprocessedFunction fun) { return fun.results.paths; });
    // TODO Do we need to take the intersection of the pathmaps here?
    const auto pathMap = pathMaps.first;
    const auto returnType = preprocessedFunctions.first.fun->getReturnType();
    const auto funArgsPair = functionArgs(*preprocessedFunctions.first.fun,
                                          *preprocessedFunctions.second.fun);
    const auto functionArguments = functionArgs(
        *preprocessedFunctions.first.fun, *preprocessedFunctions.second.fun);
    const auto freeVarsMap =
        freeVars(pathMaps.first, pathMaps.second, functionArguments);

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        MonoPair<SMTRef> invariants = invariantDeclaration(
            startIndex, freeVarsMap.at(startIndex), ProgramSelection::Both,
            functionName, returnType);
        declarations.push_back(std::move(invariants.first));
        declarations.push_back(std::move(invariants.second));
    }
    return declarations;
}

vector<SharedSMTRef>
functionalFunctionDeclarations(PreprocessedFunction preprocessedFunction,
                               Program prog) {
    const string functionName = preprocessedFunction.fun->getName().str();
    const auto pathMap = preprocessedFunction.results.paths;
    const auto returnType = preprocessedFunction.fun->getReturnType();
    const auto functionArguments = functionArgs(*preprocessedFunction.fun);
    const auto freeVarsMap = freeVars(pathMap, functionArguments, prog);

    vector<SharedSMTRef> declarations;
    for (const auto &pathMapIt : pathMap) {
        const int startIndex = pathMapIt.first;
        MonoPair<SMTRef> invariants =
            invariantDeclaration(startIndex, freeVarsMap.at(startIndex),
                                 asSelection(prog), functionName, returnType);
        declarations.push_back(std::move(invariants.first));
        declarations.push_back(std::move(invariants.second));
    }
    return declarations;
}
