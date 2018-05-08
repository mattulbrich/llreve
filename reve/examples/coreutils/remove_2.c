/*@ rel_in (and (= fd$1 fd$2) (= file$1 file$2) (= st_size$1 st_size$2) (= st_ino$1 st_ino$2) (= flag$1 flag$2) (= errno$1 errno$2) (= fstatat$1 fstatat$2) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (>= file$1 0) (>= errno$1 0) (>= fstatat$1 0) (>= file$2 0) (>= errno$2 0) (>= fstatat$2 0) (distinct st_size$1 (- 1)) (= st_ino$2 (- (- 1) st_size$1))) @*/
/* Like fstatat, but cache the result.  If st_size is -1, the
   status has not been gotten yet.  If less than -1, fstatat failed
   with errno == -1 - st_size.  Otherwise, the status has already
   been gotten, so return 0.  */
int cache_fstatat(int fd, char const *file, int st_size, int st_ino, int flag,
                  int *errno, int *fstatat) {
    if (st_size == -1 && *fstatat != 0) {
        st_size = -2;
        st_ino = *errno;
    }
    if (0 <= st_size)
        return 0;
    *errno = (int)st_ino;
    return -1;
}
