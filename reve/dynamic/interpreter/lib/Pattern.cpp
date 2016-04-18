#include "Pattern.h"

using std::ostream;
using std::vector;
using std::string;
using namespace pattern;

ostream &Expr::dump(ostream &os, vector<string> vec) const {
    return dump(os, vec.begin(), vec.end());
}

bool BinaryOp::matches(VecIter begin, VecIter end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    switch (op) {
    case Operation::Eq: {
        VecIter mid = begin + static_cast<long>(args.first->arguments());
        VarIntVal left = args.first->eval(begin, mid);
        VarIntVal right = args.second->eval(mid, end);
        return left == right;
    }
    case Operation::Add:
        logWarning("Matching on an addition is always true\n");
        return true;
    }
}

VarIntVal BinaryOp::eval(VecIter begin, VecIter end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    VecIter mid = begin + static_cast<long>(args.first->arguments());
    VarIntVal left = args.first->eval(begin, mid);
    VarIntVal right = args.second->eval(mid, end);
    switch (op) {
    case Operation::Eq:
        logWarning("Evaluating equality equality, converting to integer\n");
        return left == right;
    case Operation::Add:
        return left + right;
    }
}

size_t BinaryOp::arguments() const {
    return args.first->arguments() + args.second->arguments();
}

size_t BinaryOp::variables() const {
    return args.first->variables() + args.second->variables();
}

ostream &BinaryOp::dump(ostream &os, vector<string>::iterator begin,
                        vector<string>::iterator end) const {
    assert(static_cast<size_t>(end - begin) ==
           args.first->arguments() + args.second->arguments());
    vector<string>::iterator mid =
        begin + static_cast<long>(args.first->arguments());
    os << "(";
    args.first->dump(os, begin, mid);
    switch (op) {
    case Operation::Eq:
        os << " = ";
        break;
    case Operation::Add:
        os << " + ";
        break;
    }
    args.second->dump(os, mid, end);
    os << ")";
    return os;
}

bool Value::matches(VecIter begin, VecIter end) const {
    assert(end - begin == 1);
    return true;
}

VarIntVal Value::eval(VecIter begin, VecIter end) const {
    assert(end - begin == 1);
    return *begin;
}

size_t Value::arguments() const { return 1; }

size_t Value::variables() const {
    switch (val) {
    case Placeholder::Variable:
        return 1;
    case Placeholder::Constant:
        return 0;
    }
}

ostream &Value::dump(ostream &os, vector<string>::iterator begin,
                     vector<string>::iterator end) const {
    assert(end - begin == 1);
    os << *begin;
    return os;
}
