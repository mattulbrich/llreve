#include "HeapPattern.h"

using std::string;

template <>
VarIntVal Variable<string>::eval(VarMap<string> variables,
                                 MonoPair<Heap> /* unused */) const {
    return variables.at(varName)->unsafeIntVal();
}

template <> std::ostream &Variable<std::string>::dump(std::ostream &os) const {
    os << varName;
    return os;
}

VarIntVal getHeapVal(HeapAddress addr, Heap heap) {
    auto it = heap.find(addr);
    if (it != heap.end()) {
        return it->second.val;
    } else {
        return 0;
    }
}
