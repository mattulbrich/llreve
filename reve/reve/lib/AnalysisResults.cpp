#include "AnalysisResults.h"
#include "Helper.h"

using std::string;

MonoPair<PathMap> getPathMaps(MonoPair<llvm::Function *> functions,
                              const AnalysisResultsMap &analysisResults) {
    logWarning("functionNames: " + functions.first->getName().str() + ", " +
               functions.second->getName().str() + "\n");
    return makeMonoPair(analysisResults.at(functions.first).paths,
                        analysisResults.at(functions.second).paths);
}

MonoPair<BidirBlockMarkMap>
getBlockMarkMaps(MonoPair<llvm::Function *> functions,
                 const AnalysisResultsMap &analysisResults) {
    return makeMonoPair(analysisResults.at(functions.first).blockMarkMap,
                        analysisResults.at(functions.second).blockMarkMap);
}

string getFunctionName(MonoPair<llvm::Function *> functions) {
    return functions.first->getName().str() + "^" +
           functions.second->getName().str();
}
