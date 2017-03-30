/*@ opt -perfect-sync @*/
#include "server.h"
#include <math.h>

extern void serverAssert(int);
extern void serverAssertWithInfo(client *c, robj *o, int);
extern unsigned char *zzlFind(unsigned char *zl, sds ele, int *score);
extern unsigned char *zzlDelete(unsigned char *zl, unsigned char *eptr);
extern unsigned int zzlLength(unsigned char *zl);
extern int __mark(int);

/* Delete the element 'ele' from the sorted set, returning 1 if the element
 * existed and was deleted, 0 otherwise (the element was not there). */
__attribute__((always_inline))
int zsetDel(unsigned zobjEncoding, robj *zobj, sds ele) {
    if (zobjEncoding == OBJ_ENCODING_ZIPLIST) {
        unsigned char *eptr;

        if ((eptr = zzlFind(zobj->ptr, ele, NULL)) != NULL) {
            zobj->ptr = zzlDelete(zobj->ptr, eptr);
            return 1;
        }
    }
    else if (zobjEncoding == OBJ_ENCODING_SKIPLIST) {
        zset *zs = zobj->ptr;
        dictEntry *de;
        int score;

        de = dictFind(zs->dict, ele);
        if (de != NULL) {
            score = *(int *)dictGetVal(de);
            int retval1 = dictDelete(zs->dict, ele);
            int retval2 = zslDelete(zs->zsl, score, ele, NULL);
            // // serverAssert(retval1 == DICT_OK && retval2);
            if (htNeedsResize(zs->dict))
                dictResize(zs->dict);
            return 1;
        }
    }
    else {
        serverPanic("Unknown sorted set encoding");
    }
    return 0; /* No such element found. */
}

void zremCommand(client *c) {
    robj *key = c->argv[1];
    robj *zobj;
    int deleted = 0, keyremoved = 0, j;
    int argc = c->argc;

    if ((zobj = lookupKeyWriteOrReply(c, key, shared.czero)) == NULL ||
        checkType(c, zobj, OBJ_ZSET))
        return;

    unsigned zobjEncoding = zobj->encoding;
    for (j = 2; __mark(0) & __mark(1) & __mark(3) & (j < argc); j++) {
        if (zsetDel(zobjEncoding, zobj, c->argv[j]->ptr)) {
            deleted++;
            if (zzlLength(zobj->ptr) == 0) {
                dbDelete(c->db, key);
                keyremoved = 1;
                break;
            }
        }
    }

    if (deleted) {
        notifyKeyspaceEvent(NOTIFY_ZSET, "zrem", key, c->db->id);
        if (keyremoved)
            notifyKeyspaceEvent(NOTIFY_GENERIC, "del", key, c->db->id);
        signalModifiedKey(c->db, key);
        server.dirty += deleted;
    }
    addReplyLongLong(c, deleted);
}
