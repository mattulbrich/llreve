/*@ rel_in (and (= fd$1_0 fd$2_0) (= file$1_0 file$2_0) (= st_size$1_0 st_size$2_0) (= st_ino$1_0 st_ino$2_0) (= flag$1_0 flag$2_0) (= errno$1_0 errno$2_0) (= fstatat$1_0 fstatat$2_0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (>= file$1_0 0) (>= errno$1_0 0) (>= fstatat$1_0 0) (>= file$2_0 0) (>= errno$2_0 0) (>= fstatat$2_0 0) (distinct st_size$1_0 (- 1)) (= st_ino$2_0 (- (- 1) st_size$1_0))) @*/
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
