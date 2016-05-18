#include "HeapPattern.h"

template <>
VarIntVal Variable<const llvm::Value *>::eval(
    const VarMap<const llvm::Value *> &variables,
    const MonoPair<Heap> & /* unused */, const HoleMap & /* unused */) const {
    return variables.at(varName)->unsafeIntVal();
}

template <>
std::ostream &Variable<const llvm::Value *>::dump(std::ostream &os) const {
    std::string name = varName->getName();
    os << name;
    return os;
}

VarIntVal getHeapVal(HeapAddress addr, Heap heap) {
    auto it = heap.find(addr);
    if (it != heap.end()) {
        return it->second;
    } else {
        return 0;
    }
}
