#include "FreeVariables.h"

#include "Helper.h"
#include "Opts.h"

#include "llvm/IR/Instructions.h"

using smt::SortedVar;
using std::map;
using std::set;
using std::vector;

struct FreeVar {
    smt::SortedVar var;
    llvm::Type *type;
};

inline bool operator<(const FreeVar &lhs, const FreeVar &rhs) {
    return lhs.var < rhs.var;
}

inline bool operator>(const FreeVar &lhs, const FreeVar &rhs) {
    return rhs < lhs;
}

inline bool operator<=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs > rhs);
}

inline bool operator>=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs < rhs);
}

inline bool operator==(const FreeVar &lhs, const FreeVar &rhs) {
    return lhs.var == rhs.var;
}

inline bool operator!=(const FreeVar &lhs, const FreeVar &rhs) {
    return !(lhs == rhs);
}

struct VariablesResult {
    std::set<FreeVar> accessed;
    std::map<int, std::set<FreeVar>> constructed;
};

static FreeVar llvmValToFreeVar(const llvm::Value *val) {
    return {llvmValToSortedVar(val), val->getType()};
}

static void freeVarsInBlock(llvm::BasicBlock &block,
                            const llvm::BasicBlock *prev,
                            set<FreeVar> &freeVars, set<FreeVar> &constructed) {
    for (auto &instr : block) {
        constructed.insert(llvmValToFreeVar(&instr));
        if (const auto phiInst = llvm::dyn_cast<llvm::PHINode>(&instr)) {
            if (prev == nullptr) {
                // This is needed for phi nodes in a marked block since we can’t
                // resolve theme here
                freeVars.insert(llvmValToFreeVar(&instr));
            } else {
                const auto incoming = phiInst->getIncomingValueForBlock(prev);
                if (constructed.find(llvmValToFreeVar(incoming)) ==
                        constructed.end() &&
                    !incoming->getName().empty() &&
                    !llvm::isa<llvm::BasicBlock>(incoming)) {
                    freeVars.insert(llvmValToFreeVar(incoming));
                }
            }
        } else {
            for (const auto op : instr.operand_values()) {
                if (constructed.find(llvmValToFreeVar(op)) ==
                        constructed.end() &&
                    !op->getName().empty() &&
                    !llvm::isa<llvm::BasicBlock>(op) &&
                    !llvm::isa<llvm::GlobalValue>(op)) {
                    freeVars.insert(llvmValToFreeVar(op));
                }
            }
        }
    }
}
/// Collect the free variables for all paths starting at some mark
static VariablesResult freeVarsOnPaths(map<int, Paths> pathMap) {
    set<FreeVar> freeVars;
    map<int, set<FreeVar>> constructedIntersection;
    for (const auto &paths : pathMap) {
        for (const auto &path : paths.second) {
            const llvm::BasicBlock *prev = path.Start;
            set<FreeVar> constructed;

            freeVarsInBlock(*path.Start, nullptr, freeVars, constructed);

            // now deal with the rest
            for (const auto &edge : path.Edges) {
                freeVarsInBlock(*edge.Block, prev, freeVars, constructed);
                prev = edge.Block;
            }

            // A variable is constructed on a way to a mark if it is constructed
            // on all paths. We thus have to take the intersection of the
            // constructed variables.
            set<FreeVar> newConstructedIntersection;
            if (constructedIntersection.find(paths.first) ==
                constructedIntersection.end()) {
                constructedIntersection.insert(
                    make_pair(paths.first, constructed));
                ;
            } else {
                std::set_intersection(
                    constructed.begin(), constructed.end(),
                    constructedIntersection.at(paths.first).begin(),
                    constructedIntersection.at(paths.first).end(),
                    inserter(newConstructedIntersection,
                             newConstructedIntersection.begin()));
                constructedIntersection.insert(
                    make_pair(paths.first, newConstructedIntersection));
            }
        }
    }
    return {freeVars, constructedIntersection};
}

static set<SortedVar> addMemoryLocations(const set<FreeVar> &freeVars) {
    set<SortedVar> newFreeVars;
    for (const auto &var : freeVars) {
        newFreeVars.insert(var.var);
        if (SMTGenerationOpts::getInstance().Stack && var.type->isPointerTy()) {
            newFreeVars.insert({var.var.name + "_OnStack", "Bool"});
        }
    }
    return newFreeVars;
}

smt::FreeVarsMap freeVars(PathMap map1, PathMap map2,
                          vector<smt::SortedVar> funArgs) {
    return mergeVectorMaps(
        freeVars(map1, filterVars(1, funArgs), Program::First),
        freeVars(map2, filterVars(2, funArgs), Program::Second));
}

static auto addMemoryArrays(vector<smt::SortedVar> vars, Program prog)
    -> vector<smt::SortedVar> {
    int index = programIndex(prog);
    if (SMTGenerationOpts::getInstance().Heap) {
        vars.push_back(SortedVar(heapName(index), arrayType()));
    }
    if (SMTGenerationOpts::getInstance().Stack) {
        vars.push_back(SortedVar(stackPointerName(index), stackPointerType()));
        vars.push_back(SortedVar(stackName(index), arrayType()));
    }
    return vars;
}
smt::FreeVarsMap freeVars(PathMap map, vector<smt::SortedVar> funArgs,
                          Program prog) {
    std::map<int, set<SortedVar>> freeVarsMap;
    smt::FreeVarsMap freeVarsMapVect;
    std::map<int, std::map<int, set<SortedVar>>> constructed;
    for (const auto &it : map) {
        const int index = it.first;
        auto freeVarsResult = freeVarsOnPaths(map.at(index));

        const auto accessed = addMemoryLocations(freeVarsResult.accessed);
        freeVarsMap.insert(make_pair(index, accessed));

        std::map<int, set<SortedVar>> constructedVarsMap;
        for (const auto &it : freeVarsResult.constructed) {
            const auto constructedVars = addMemoryLocations(it.second);
            constructedVarsMap.insert({it.first, constructedVars});
        }

        constructed.insert(make_pair(index, constructedVarsMap));
    }

    freeVarsMap[EXIT_MARK] = {};
    if (SMTGenerationOpts::getInstance().PassInputThrough) {
        for (const auto &arg : funArgs) {
            freeVarsMap[EXIT_MARK].insert(arg);
        }
    }
    freeVarsMap[UNREACHABLE_MARK] = {};

    // search for a least fixpoint
    bool changed = true;
    while (changed) {
        changed = false;
        for (const auto &it : map) {
            const int startIndex = it.first;
            for (const auto &itInner : it.second) {
                const int endIndex = itInner.first;
                for (auto var : freeVarsMap.at(endIndex)) {
                    if (constructed.at(startIndex).at(endIndex).find(var) ==
                        constructed.at(startIndex).at(endIndex).end()) {
                        const auto inserted =
                            freeVarsMap.at(startIndex).insert(var);
                        changed = changed || inserted.second;
                    }
                }
            }
        }
    }

    for (auto it : freeVarsMap) {
        const int index = it.first;
        vector<smt::SortedVar> varsVect;
        for (const auto &var : it.second) {
            varsVect.push_back(var);
        }
        freeVarsMapVect[index] = addMemoryArrays(varsVect, prog);
    }

    // The input arguments should be in the function argument order so we can’t
    // add them before
    freeVarsMapVect[ENTRY_MARK] = addMemoryArrays(funArgs, prog);

    return freeVarsMapVect;
}
