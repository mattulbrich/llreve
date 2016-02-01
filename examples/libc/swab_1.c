/* dietlibc */
#include <unistd.h>
extern int __mark(int);
void swab(const void *src, void *dest, ssize_t nbytes) {
    ssize_t i;
    const char *s = src;
    char *d = dest;
    // CHANGED
    nbytes = (nbytes / 2) * 2;
    for (i = 0; __mark(0) & (i < nbytes); i += 2) {
        d[i] = s[i + 1];
        d[i + 1] = s[i];
    }
}
