typedef int uid_t;
typedef int gid_t;

extern int HAVE_FCHOWN();
extern int error(int, int, int, int);
extern int quote(char const *);

/* Set the owner and owning group of DEST_DESC to the st_uid and
   st_gid fields of SRC_SB.  If DEST_DESC is undefined (-1), set
   the owner and owning group of DST_NAME instead.  DEST_DESC must
   refer to the same file as DEST_NAME if defined.
   Return 1 if the syscall succeeds, 0 if it fails but it's OK
   not to preserve ownership, -1 otherwise.  */

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
            r = -1;
            return r;
        }
    }

    r = 0;
    return r;
}
