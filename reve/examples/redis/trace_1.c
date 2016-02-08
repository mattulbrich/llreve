#include <lua.h>
#include <string.h>

typedef char *sds;
extern void ldbLog(sds entry);
extern void ldbLogSourceLine(int lnum);
extern sds sdsnew(const char *init);
extern sds sdscatprintf(sds s, const char *fmt, const char*, const char*);
extern sds sdsempty(void);

/*@ addfuncond strstr
(distinct res1 0)
 @*/
extern int __mark(int);

void ldbTrace(lua_State *lua) {
    lua_Debug ar;
    int level = 0;

    while(__mark(0) & lua_getstack(lua,level,&ar)) {
        lua_getinfo(lua,"Snl",&ar);
        // This results in an infinite loop which is pretty bad
        if(strstr(ar.short_src,"user_script") == NULL) continue;
        ldbLog(sdscatprintf(sdsempty(),"%s %s:",
            (level == 0) ? "In" : "From",
            ar.name ? ar.name : "top level"));
        ldbLogSourceLine(ar.currentline);
        level++;
    }
    if (level == 0) {
        ldbLog(sdsnew("<error> Can't retrieve Lua stack."));
    }
}
