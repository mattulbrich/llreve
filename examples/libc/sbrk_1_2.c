/* dietlibc */
#include <unistd.h>
#include <stdint.h>
#include <errno.h>
#include <stddef.h>
extern int __mark(int);
extern int __libc_brk(void *end_data_segment);

extern void *__curbrk;

void *sbrk(ptrdiff_t increment) {
    void *oldbrk;
    if (__curbrk == 0)
        if (__libc_brk(0) < 0)
            return (void *)-1;
    if (increment == 0)
        return __curbrk;
    __mark(0);
    oldbrk = __curbrk;
    if (__libc_brk((char *)oldbrk + increment) < 0)
        return (void *)-1;
    return oldbrk;
}
