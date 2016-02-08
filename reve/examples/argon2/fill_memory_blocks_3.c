// unknown
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "core.h"
#include "thread.h"

extern int __mark(int);

void fill_memory_blocks(argon2_instance_t *instance) {
    uint32_t r;
    argon2_thread_handle_t *thread = NULL;

    thread = calloc(instance->lanes, sizeof(argon2_thread_handle_t));
    if (thread == NULL) {
        return;
    }

    for (r = 0; __mark(0) & (r < instance->passes); ++r) {
    }
}
