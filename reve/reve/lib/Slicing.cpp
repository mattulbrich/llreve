#include "Slicing.h"

#include "Compat.h"
#include "Helper.h"
#include "Invariant.h"

using smt::FunDef;
using smt::makeOp;
using smt::Op;
using smt::SharedSMTRef;
using smt::SortedVar;
using smt::stringExpr;
using std::make_shared;
using std::string;
using std::vector;

vector<SharedSMTRef> slicingAssertion(MonoPair<PreprocessedFunction> funPair) {
    vector<SharedSMTRef> assertions;

    string typeBool = "Bool";
    string typeInt = "Int";
    std::string name;

    // Collect arguments for call
    std::vector<SortedVar> args;

    auto funArgs1 = functionArgs(*(funPair.first.fun));
    auto funArgs2 = functionArgs(*(funPair.second.fun));
    assert(funArgs1.size() == funArgs2.size());

    args.insert(args.end(), funArgs1.begin(), funArgs1.end());
    args.insert(args.end(), funArgs2.begin(), funArgs2.end());

    // Set preconditition for nonmutual calls to false. This ensures
    // that only mutual calls are allowed.
    // Note that we assume the number of arguments to be equal (number of
    // variables in the criterion). This is why we can use the same arg names.
    makeMonoPair(funArgs1, funArgs2)
        .indexedForEachProgram([&assertions, typeBool](auto funArgs,
                                                       auto program) {
            std::string invName =
                invariantName(ENTRY_MARK, asSelection(program), "__criterion",
                              InvariantAttr::PRE, 0);
            assertions.push_back(make_shared<FunDef>(invName, funArgs, typeBool,
                                                     stringExpr("false")));
        });

    // Ensure all variables in the criterion are equal in both versions
    // of the program using the mutual precondition
    vector<SharedSMTRef> equalArgs;
    for (auto argPair : makeZip(funArgs1, funArgs2)) {
        equalArgs.push_back(
            makeOp("=", argPair.first.name, argPair.second.name));
    }

    SharedSMTRef allEqual = make_shared<Op>("and", equalArgs);
    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::PRE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, typeBool, allEqual));

    // Finaly we need to set the invariant for the function itself to true.
    // (The __criterion function does nothing, therefore no restrictions arise)
    // This is true for mutual and non mutual calls.
    args.push_back(SortedVar("ret1", typeInt));
    args.push_back(SortedVar("ret2", typeInt));

    SharedSMTRef invBody = stringExpr("true");
    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::NONE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, typeBool, invBody));

    makeMonoPair(funArgs1, funArgs2)
        .indexedForEachProgram([&assertions, &invBody, typeInt,
                                typeBool](auto funArgs, auto program) {
            funArgs.push_back(SortedVar(
                "ret" + std::to_string(programIndex(program)), typeInt));
            std::string invName =
                invariantName(ENTRY_MARK, asSelection(program), "__criterion",
                              InvariantAttr::NONE, 0);
            assertions.push_back(
                make_shared<FunDef>(invName, funArgs, typeBool, invBody));
        });

    return assertions;
}
