// out of memory during preprocessing
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "core.h"
#include "thread.h"
#include "blake2.h"

extern void *fill_segment_thr(void *thread_data);
extern int __mark(int);

void fill_memory_blocks(argon2_instance_t *instance) {
    uint32_t r, s;
    argon2_thread_handle_t *thread = NULL;
    argon2_thread_data *thr_data = NULL;

    if (instance == NULL || instance->lanes == 0) {
        return;
    }

    /* 1. Allocating space for threads */
    thread = calloc(instance->lanes, sizeof(argon2_thread_handle_t));
    if (thread == NULL) {
        return;
    }

    thr_data = calloc(instance->lanes, sizeof(argon2_thread_data));
    if (thr_data == NULL) {
        free(thread);
        return;
    }

    for (r = 0; __mark(0) & (r < instance->passes); ++r) {
        for (s = 0; __mark(1) & (s < ARGON2_SYNC_POINTS); ++s) {
            int rc;
            uint32_t l;

            /* 2. Calling threads */
            for (l = 0; __mark(2) & (l < instance->lanes); ++l) {
                argon2_position_t position;

                /* 2.1 Join a thread if limit is exceeded */
                if (l >= instance->threads) {
                    rc = argon2_thread_join(thread[l - instance->threads]);
                    if (rc) {
                        // CHANGED: I hate varargs
                        printf("ERROR; return code from pthread_join() #1 is % d\n",
                               rc);
                        exit(-1);
                    }
                }

                /* 2.2 Create thread */
                position.pass = r;
                position.lane = l;
                position.slice = (uint8_t)s;
                position.index = 0;
                thr_data[l].instance_ptr =
                    instance; /* preparing the thread input */
                memcpy(&(thr_data[l].pos), &position,
                       sizeof(argon2_position_t));
                // CHANGED: no support for function pointers
                rc = argon2_thread_create(&thread[l],
                                          NULL /* &fill_segment_thr */,
                                          (void *)&thr_data[l]);
                if (rc) {
                    // CHANGED: I still hate varargs
                    printf("ERROR; return code from argon2_thread_create() is %d\n",
                           rc);
                    exit(-1);
                }

                /* fill_segment(instance, position); */
                /*Non-thread equivalent of the lines above */
            }

            /* 3. Joining remaining threads */
            for (l = instance->lanes - instance->threads;
                 __mark(3) & (l < instance->lanes); ++l) {
                rc = argon2_thread_join(thread[l]);
                if (rc) {
                    // CHANGED: By now you should know my opinion about varargs
                    printf("ERROR; return code from pthread_join() is %d\n",
                           rc);
                    exit(-1);
                }
            }
        }
    }

    if (thread != NULL) {
        free(thread);
    }
    if (thr_data != NULL) {
        free(thr_data);
    }
}
