#include "Slicing.h"

#include "Compat.h"
#include "Helper.h"
#include "Invariant.h"
#include "Opts.h"

using std::make_unique;
using std::make_shared;
using std::string;
using std::vector;

using namespace smt;
using namespace llreve::opts;
using namespace llreve;

vector<SharedSMTRef>
slicingAssertion(MonoPair<llvm::Function *> funPair,
                 const AnalysisResultsMap &analysisResults) {
    SharedSMTRef invBody = nullptr;
    vector<SharedSMTRef> assertions;
    std::string name;

    // Collect arguments for call
    std::vector<SortedVar> args;

    auto funArgs1 = analysisResults.at(funPair.first).functionArguments;
    auto funArgs2 = analysisResults.at(funPair.second).functionArguments;
    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        funArgs1.push_back(SortedVar("heap_idx$1", int64Type()));
        funArgs1.push_back(SortedVar("heap_val$1", int64Type()));

        funArgs2.push_back(SortedVar("heap_idx$2", int64Type()));
        funArgs2.push_back(SortedVar("heap_val$2", int64Type()));
    }
    assert(funArgs1.size() == funArgs2.size());

    args.insert(args.end(), funArgs1.begin(), funArgs1.end());
    args.insert(args.end(), funArgs2.begin(), funArgs2.end());

    // This body is equal to false. We cahnt use false as eldarica would crash
    invBody = makeOp("not", makeOp("=", funArgs1.begin()->name, funArgs1.begin()->name));

    // Set preconditition for nonmutual calls to false. This ensures
    // that only mutual calls are allowed.
    // Note that we assume the number of arguments to be equal (number of
    // variables in the criterion). This is why we can use the same arg names.
    makeMonoPair(funArgs1, funArgs2)
        .indexedForEachProgram([&assertions,&invBody](auto funArgs, auto program) {
            std::string invName =
                invariantName(ENTRY_MARK, asSelection(program), "__criterion",
                              InvariantAttr::PRE, 0);
            assertions.push_back(
                make_shared<FunDef>(invName, funArgs, boolType(),
                                    invBody));
        });

    // Ensure all variables in the criterion are equal in both versions
    // of the program using the mutual precondition
    vector<SharedSMTRef> equalArgs;
    for (auto argPair : makeZip(funArgs1, funArgs2)) {
        if ((argPair.first.name != "heap_idx$1")
            && argPair.first.name != "heap_val$1") {
            equalArgs.push_back(
                makeOp("=", argPair.first.name, argPair.second.name));
        }
    }

    SharedSMTRef allEqual = make_shared<Op>("and", equalArgs);
    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::PRE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, boolType(), allEqual));

    // Finaly we need to set the invariant for the function itself to true.
    // (The __criterion function does nothing, therefore no restrictions arise)
    // This is true for mutual and non mutual calls.
    args.push_back(SortedVar("ret$1", int64Type()));
    args.push_back(SortedVar("ret$2", int64Type()));

    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        args.push_back(SortedVar("heap_idx$1_res", int64Type()));
        args.push_back(SortedVar("heap_val$1_res", int64Type()));
        args.push_back(SortedVar("heap_idx$2_res", int64Type()));
        args.push_back(SortedVar("heap_val$2_res", int64Type()));
    }

    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        vector<SharedSMTRef> equalArgs;
        equalArgs.push_back(
            makeOp("=>",
                makeOp("=", "heap_idx$1", "heap_idx$1_res"),
                makeOp("=", "heap_val$1", "heap_val$1_res")));
        equalArgs.push_back(
            makeOp("=>",
                makeOp("=", "heap_idx$2", "heap_idx$2_res"),
                makeOp("=", "heap_val$2", "heap_val$2_res")));
        invBody = make_shared<Op>("and", equalArgs);
    } else {
        invBody = make_unique<ConstantBool>(true);
    }

    name = invariantName(ENTRY_MARK, ProgramSelection::Both, "__criterion",
                         InvariantAttr::NONE, 0);
    assertions.push_back(make_shared<FunDef>(name, args, boolType(), invBody));

    if (SMTGenerationOpts::getInstance().Heap == HeapOpt::Enabled) {
        vector<SharedSMTRef> equalArgs;
        equalArgs.push_back(
            makeOp("=>",
                makeOp("=", "heap_idx$1", "heap_idx$1_res"),
                makeOp("=", "heap_val$1", "heap_val$1_res")));
        invBody = make_shared<Op>("and", equalArgs);
    } else {
        invBody = stringExpr("true");
    }

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
