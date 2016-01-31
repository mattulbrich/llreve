/* dietlibc */
#include <stddef.h>
extern int __mark(int);
void* memset(void * dst, int s, size_t count) {
    register char * a = dst;
    count++;	/* this actually creates smaller code than using count-- */
    while (--count) {
        *a++ = s;
        __mark(0);
    }
    return dst;
}
