#include "Slicing.h"

#include "Compat.h"
#include "Helper.h"
#include "Invariant.h"

using std::make_unique;
using std::make_shared;
using std::string;
using std::vector;

using namespace smt;

vector<SharedSMTRef>
slicingAssertion(MonoPair<llvm::Function *> funPair,
                 const AnalysisResultsMap &analysisResults) {
    vector<SharedSMTRef> assertions;

    std::string name;

    // Collect arguments for call
    std::vector<SortedVar> args;

    auto funArgs1 = analysisResults.at(funPair.first).functionArguments;
    auto funArgs2 = analysisResults.at(funPair.second).functionArguments;
    assert(funArgs1.size() == funArgs2.size());

    args.insert(args.end(), funArgs1.begin(), funArgs1.end());
    args.insert(args.end(), funArgs2.begin(), funArgs2.end());

    // Set preconditition for nonmutual calls to false. This ensures
    // that only mutual calls are allowed.
    // Note that we assume the number of arguments to be equal (number of
    // variables in the criterion). This is why we can use the same arg names.
    makeMonoPair(funArgs1, funArgs2)
        .indexedForEachProgram([&assertions](auto funArgs, auto program) {
            std::string invName =
                invariantName(ENTRY_MARK, asSelection(program), "__criterion",
                              InvariantAttr::PRE, 0);
            assertions.push_back(
                make_shared<FunDef>(invName, funArgs, boolType(),
                                    make_unique<ConstantBool>(false)));
        });

    // Ensure all variables in the criterion are equal in both versions
    // of the program using the mutual precondition
    vector<SharedSMTRef> equalArgs;
    std::transform(funArgs1.begin(), funArgs1.end(), funArgs2.begin(),
                   std::back_inserter(equalArgs),
                   [](const auto &arg1, const auto &arg2) {
                       return makeOp("=", arg1.name, arg2.name);
                   });

    SharedSMTRef allEqual = make_shared<Op>("and", equalArgs);
    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::PRE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, boolType(), allEqual));

    // Finaly we need to set the invariant for the function itself to true.
    // (The __criterion function does nothing, therefore no restrictions arise)
    // This is true for mutual and non mutual calls.
    args.push_back(SortedVar("ret1", int64Type()));
    args.push_back(SortedVar("ret2", int64Type()));

    SharedSMTRef invBody = make_unique<ConstantBool>(true);
    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::NONE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, boolType(), invBody));

    makeMonoPair(funArgs1, funArgs2)
        .indexedForEachProgram([&assertions, &invBody](auto funArgs,
                                                       auto program) {
            funArgs.push_back(SortedVar(
                "ret" + std::to_string(programIndex(program)), int64Type()));
            std::string invName =
                invariantName(ENTRY_MARK, asSelection(program), "__criterion",
                              InvariantAttr::NONE, 0);
            assertions.push_back(
                make_shared<FunDef>(invName, funArgs, boolType(), invBody));
        });

    return assertions;
}
