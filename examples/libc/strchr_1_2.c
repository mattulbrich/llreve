/* dietlibc */
extern int __mark(int);
char *strchr(register const char *t, int c) {
    register char ch;

    ch = c;
    for (;__mark(42);) {
        if (*t == ch)
            break;
        if (!*t)
            return 0;
        ++t;
        if (*t == ch)
            break;
        if (!*t)
            return 0;
        ++t;
        if (*t == ch)
            break;
        if (!*t)
            return 0;
        ++t;
    }
    return (char *)t;
}
