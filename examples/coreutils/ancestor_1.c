#include <sys/stat.h>
#include <sys/types.h>
#include <stdbool.h>

extern int __mark(int);

struct dir_list {
    struct dir_list *parent;
    ino_t ino;
    dev_t dev;
};

bool is_ancestor(const struct stat *sb, const struct dir_list *ancestors) {
    while (__mark(42) & (ancestors != 0)) {
        if (ancestors->ino == sb->st_ino && ancestors->dev == sb->st_dev)
            return true;
        ancestors = ancestors->parent;
    }
    return false;
}
