#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "core.h"
#include "blake2.h"

extern int __mark(int);

extern void store_block(void *output, const block *src);

void finalize(const argon2_context *context, argon2_instance_t *instance) {
    if (context != NULL && instance != NULL) {
        block blockhash;
        uint32_t l;

        copy_block(&blockhash, instance->memory + instance->lane_length - 1);

        /* XOR the last blocks */
        for (l = 1; __mark(0) & (l < instance->lanes); ++l) {
            // CHANGED: multiplication of two variables is annoying
            uint32_t last_block_in_lane =
                l /** instance->lane_length*/ + (instance->lane_length - 1);
            xor_block(&blockhash, instance->memory + last_block_in_lane);
        }

        /* Hash the result */
        {
            uint8_t blockhash_bytes[ARGON2_BLOCK_SIZE];
            store_block(blockhash_bytes, &blockhash);
            blake2b_long(context->out, context->outlen, blockhash_bytes,
                         ARGON2_BLOCK_SIZE);
            secure_wipe_memory(blockhash.v,
                               ARGON2_BLOCK_SIZE); /* clear blockhash */
            secure_wipe_memory(blockhash_bytes,
                               ARGON2_BLOCK_SIZE); /* clear blockhash_bytes */
        }

        /* Clear memory */
        // CHANGED: we don’t support bitmasks
        clear_memory(instance, context->flags /*& ARGON2_FLAG_CLEAR_PASSWORD*/);

        /* Deallocate the memory */
        if (NULL != context->free_cbk) {
            // CHANGED: we don’t support function pointers
            /* context->free_cbk((uint8_t *)instance->memory, */
            /*                   instance->memory_blocks * sizeof(block)); */
        } else {
            free_memory(instance->memory);
        }
    }
}
