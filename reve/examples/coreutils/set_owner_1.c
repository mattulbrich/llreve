/*@ rel_in (and (= dst_name$1 dst_name$2) (= dest_desc$1 dest_desc$2) (= uid$1 uid$2) (= gid$1 gid$2) (= fchown_dest_desc_uid_gid$1 fchown_dest_desc_uid_gid$2) (= chown_dst_name_uid_gid$1 chown_dst_name_uid_gid$2) (= chown_failure_ok_x$1 chown_failure_ok_x$2) (= x_require_preserve$1 x_require_preserve$2) (= errno$1 errno$2) (= fchown_dest_desc_uid_gid$1 0) (= chown_dst_name_uid_gid$1 0) (forall ((i Int)) (= (select HEAP$1 i) (select HEAP$2 i))) (>= dst_name$1 0) (>= dst_name$2 0)) @*/
typedef int uid_t;
typedef int gid_t;

extern int HAVE_FCHOWN();
extern int error(int, int, int, int);
extern int quote(char const *);

/* Set the owner and owning group of DEST_DESC to the st_uid and
   st_gid fields of SRC_SB.  If DEST_DESC is undefined (-1), set
   the owner and owning group of DST_NAME instead.  DEST_DESC must
   refer to the same file as DEST_NAME if defined.
   Return true if the syscall succeeds, or if it's ok not to
   preserve ownership.  */

int set_owner(char const *dst_name, int dest_desc, uid_t uid, gid_t gid,
              int fchown_dest_desc_uid_gid, int chown_dst_name_uid_gid,
              int chown_failure_ok_x, int x_require_preserve, int errno) {
    int r = 1;
    if (HAVE_FCHOWN() && dest_desc != -1) {
        if (fchown_dest_desc_uid_gid == 0) {
            return r;
        }
    } else {
        if (chown_dst_name_uid_gid == 0) {
            return r;
        }
    }

    if (!chown_failure_ok_x) {
        error(0, errno, 0, quote(dst_name));
        if (x_require_preserve) {
            return r;
        }
    }

    return r;
}
