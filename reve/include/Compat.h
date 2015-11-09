#ifndef COMPAT_H
#define COMPAT_H

template<class T> class Reverse {
private:
    T t;
public:
    Reverse(T t) : t(t) {}
    auto begin() -> decltype(t.rbegin()) {
        return t.rbegin();
    }
    auto end() -> decltype(t.rend()) {
        return t.rend();
    }
};

template<class T> Reverse<T> makeReverse(T t) {
    return Reverse<T>(t);
}

#endif // COMPAT_H
