extern int __mark(int);
int strcmp(const char *s1, const char *s2) {
    while (*s1 == *s2++) {
        if (*s1++ == 0)
            return (0);
        __mark(42);
    }
    return (*(unsigned char *)s1 - *(unsigned char *)--s2);
}
