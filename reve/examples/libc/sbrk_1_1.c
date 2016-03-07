/*@ opt -signed @*/
/* glibc */
#include <unistd.h>
#include <stdint.h>
#include <stddef.h>
#define ENOMEM 42
extern int __mark(int);
extern int __set_errno(int);
extern int __libc_brk(void *end_data_segment);

extern void *__curbrk;

void *sbrk(ptrdiff_t increment) {
    void *oldbrk;

    /* If this is not part of the dynamic library or the library is used
       via dynamic loading in a statically linked program update
       __curbrk from the kernel's brk value.  That way two separate
       instances of __libc_brk and __sbrk can share the heap, returning
       interleaved pieces of it.  */
    if (__curbrk == NULL /*|| __libc_multiple_libcs*/)
        if (__libc_brk(0) < 0) /* Initialize the break.  */
            return (void *)-1;

    if (increment == 0)
        return __curbrk;

    __mark(0);
    oldbrk = __curbrk;
    // moritz: look like overflow prevention, without overflows the
    // first one is never true so we can let it in and it’s still
    // equal to the dietlibc version
    if (increment > 0 &&
        /*?*/ ((uintptr_t)oldbrk + (uintptr_t)increment < (uintptr_t)oldbrk)
        /*: ((uintptr_t)oldbrk < (uintptr_t)-increment)*/) {
        __set_errno(ENOMEM);
        return (void *)-1;
    }

    if (__libc_brk(oldbrk + increment) < 0)
        return (void *)-1;

    return oldbrk;
}
