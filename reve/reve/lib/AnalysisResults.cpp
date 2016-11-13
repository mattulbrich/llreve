#include "AnalysisResults.h"
#include "Helper.h"

using smt::SortedVar;
using std::vector;
using std::string;

MonoPair<PathMap> getPathMaps(MonoPair<const llvm::Function *> functions,
                              const AnalysisResultsMap &analysisResults) {
    return makeMonoPair(analysisResults.at(functions.first).paths,
                        analysisResults.at(functions.second).paths);
}

MonoPair<BidirBlockMarkMap>
getBlockMarkMaps(MonoPair<const llvm::Function *> functions,
                 const AnalysisResultsMap &analysisResults) {
    return makeMonoPair(analysisResults.at(functions.first).blockMarkMap,
                        analysisResults.at(functions.second).blockMarkMap);
}

MonoPair<vector<SortedVar>>
getFunctionArguments(MonoPair<const llvm::Function *> functions,
                     const AnalysisResultsMap &analysisResults) {
    return {analysisResults.at(functions.first).functionArguments,
            analysisResults.at(functions.second).functionArguments};
}

FreeVarsMap getFreeVarsMap(MonoPair<const llvm::Function *> functions,
                           const AnalysisResultsMap &analysisResults) {
    return mergeVectorMaps(analysisResults.at(functions.first).freeVariables,
                           analysisResults.at(functions.second).freeVariables);
}

MonoPair<FreeVarsMap>
getFreeVarsPair(MonoPair<const llvm::Function *> functions,
                const AnalysisResultsMap &analysisResults) {
    return {analysisResults.at(functions.first).freeVariables,
            analysisResults.at(functions.second).freeVariables};
}

string getFunctionName(MonoPair<const llvm::Function *> functions) {
    return functions.first->getName().str() + "^" +
           functions.second->getName().str();
}
