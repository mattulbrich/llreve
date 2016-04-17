#pragma once

// Contains A, B or both
template <typename A, typename B> class These {
  private:
    std::vector<A> as;
    std::vector<B> bs;

  public:
    These(const A &a) : as({a}) {}
    These(const B &b) : bs({b}) {}
    These(const A &a, const B &b) : as({a}), bs({b}) {}
    bool hasA() { return as.size() == 1; }
    bool hasB() { return bs.size() == 1; }
    const A &getUnsafeA() { return as.front(); }
    const B &getUnsafeB() { return bs.front(); }
    std::pair<A, B> getUnsafeBoth() {
        return std::make_pair(as.front(), bs.front());
    }
    std::pair<llvm::Optional<A>, llvm::Optional<B>> getBoth() {
        llvm::Optional<A> a;
        llvm::Optional<B> b;
        if (hasA()) {
            a = llvm::Optional<A>(as.front());
        }
        if (hasB()) {
            b = llvm::Optional<B>(bs.front());
        }
        return std::make_pair(a, b);
    }
};
