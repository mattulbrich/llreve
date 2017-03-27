#include "server.h"
#include <math.h>

extern void serverPanic(const char*);
extern void serverAssertWithInfo(client *c, robj *o, int);
extern unsigned char *zzlFind(unsigned char *zl, sds ele, int *score);
extern unsigned char *zzlDelete(unsigned char *zl, unsigned char *eptr);
extern unsigned int zzlLength(unsigned char *zl);
extern int __mark(int);

void zremCommand(client *c) {
    robj *key = c->argv[1];
    robj *zobj;
    int deleted = 0, keyremoved = 0, j;

    if ((zobj = lookupKeyWriteOrReply(c, key, shared.czero)) == NULL ||
        checkType(c, zobj, OBJ_ZSET))
        return;

    if (zobj->encoding != OBJ_ENCODING_ZIPLIST && zobj->encoding != OBJ_ENCODING_SKIPLIST) {
        return;
    }
    if (zobj->encoding == OBJ_ENCODING_ZIPLIST) {
        unsigned char *eptr;

        for (j = 2; __mark(0) & (j < c->argc); j++) {
            if ((eptr = zzlFind(zobj->ptr, c->argv[j]->ptr, NULL)) != NULL) {
                deleted++;
                zobj->ptr = zzlDelete(zobj->ptr, eptr);
                if (zzlLength(zobj->ptr) == 0) {
                    dbDelete(c->db, key);
                    keyremoved = 1;
                    break;
                }
            }
        }
    }
     else if (zobj->encoding == OBJ_ENCODING_SKIPLIST) {
        for (j = 2; __mark(1) & (j < c->argc); j++) {
            zset *zs = zobj->ptr;
            dictEntry *de;
            int score;
            sds ele = c->argv[j]->ptr;
            de = dictFind(zs->dict, ele);
            if (de != NULL) {
                deleted++;
                score = *(int *)dictGetVal(de);
                int retval1 = dictDelete(zs->dict, ele);
                int retval2 = zslDelete(zs->zsl, score, ele, NULL);
                // serverAssertWithInfo(c, c->argv[j],
                //                      retval1 == DICT_OK && retval2);
                if (htNeedsResize(zs->dict))
                    dictResize(zs->dict);
                if (zzlLength(zobj->ptr) == 0) {
                    dbDelete(c->db, key);
                    keyremoved = 1;
                    break;
                }
            }
        }
    }
    // else {
    //     serverPanic("Unknown sorted set encoding");
    // }

    if (deleted) {
        notifyKeyspaceEvent(NOTIFY_ZSET, "zrem", key, c->db->id);
        if (keyremoved)
            notifyKeyspaceEvent(NOTIFY_GENERIC, "del", key, c->db->id);
        signalModifiedKey(c->db, key);
        server.dirty += deleted;
    }
    addReplyLongLong(c, deleted);
}
