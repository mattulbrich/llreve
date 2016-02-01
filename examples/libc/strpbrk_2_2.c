/* dietlibc */
extern int __mark(int);
char *strpbrk(const char *s, const char *accept) {
    register unsigned int i;
    for (; __mark(0) & (*s); s++)
        for (i = 0; __mark(1) & accept[i]; i++)
            if (*s == accept[i])
                return (char *)s;
    return 0;
}
