/* dietlibc */
extern int __mark(int);
char *stpcpy(char *dst, const char *src) {
    while (__mark(0) & (*dst++ = *src++))
        ;
    return (dst - 1);
}
