#ifndef SEXPR_H
#define SEXPR_H

#include <algorithm>
#include <memory>
#include <ostream>
#include <vector>

template <typename T> class SExpr {
  public:
    virtual void serialize(std::ostream &OS) const = 0;
    virtual ~SExpr() {}
    SExpr() {}
    SExpr(SExpr &SExpr) {}
};

template <typename T> class Value : public SExpr<T> {
  public:
    Value(T Val_) : Val(Val_) {}
    void serialize(std::ostream &OS) const { OS << Val; }
    T Val;
};

template <typename T> class Apply : public SExpr<T> {
  public:
    Apply(T Fun_, std::vector<std::shared_ptr<SExpr<T>>> Args_)
        : Fun(Fun_), Args(Args_) {}
    void serialize(std::ostream &OS) const {
        OS << "(" << Fun;
        for (auto &Arg : Args) {
            OS << " " << *Arg;
        }
        OS << ")";
    }
    T Fun;
    std::vector<std::shared_ptr<SExpr<T>>> Args;
};

template <typename T>
std::ostream &operator<<(std::ostream &OS, const SExpr<T> &Val) {
    Val.serialize(OS);
    return OS;
}

#endif // SEXPR_H
