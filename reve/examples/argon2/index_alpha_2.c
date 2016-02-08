#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "core.h"
#include "blake2.h"

uint32_t index_alpha(const argon2_instance_t *instance,
                     const argon2_position_t *position, uint32_t pseudo_rand,
                     int same_lane) {
    /*
     * Pass 0:
     *      This lane : all already finished segments plus already constructed
     * blocks in this segment
     *      Other lanes : all already finished segments
     * Pass 1+:
     *      This lane : (SYNC_POINTS - 1) last segments plus already constructed
     * blocks in this segment
     *      Other lanes : (SYNC_POINTS - 1) last segments
     */
    uint32_t reference_area_size;
    uint64_t relative_position;
    uint32_t start_position, absolute_position;

    if (0 == position->pass) {
        /* First pass */
        if (0 == position->slice) {
            /* First slice */
            reference_area_size =
                position->index - 1; /* all but the previous */
        } else {
            if (same_lane) {
                /* The same lane => add current segment */
                // CHANGED: Only multiplication with constants is supported
                reference_area_size =
                    position->slice /* * instance->segment_length*/ +
                    position->index - 1;
            } else {
                // CHANGED: Only multiplication with constants is supported
                reference_area_size =
                    position->slice /* * instance->segment_length */ +
                    ((position->index == 0) ? (-1) : 0);
            }
        }
    } else {
        /* Second pass */
        if (same_lane) {
            reference_area_size = instance->lane_length -
                                  instance->segment_length + position->index -
                                  1;
        } else {
            reference_area_size = instance->lane_length -
                                  instance->segment_length +
                                  ((position->index == 0) ? (-1) : 0);
        }
    }

    /* 1.2.4. Mapping pseudo_rand to 0..<reference_area_size-1> and produce
     * relative position */
    relative_position = pseudo_rand;
    // CHANGED: bitshifts are stupid
    /* relative_position = relative_position * relative_position >> 32; */
    /* relative_position = reference_area_size - 1 - */
    /*                     (reference_area_size * relative_position >> 32); */

    /* 1.2.5 Computing starting position */
    start_position = 0;

    if (0 != position->pass) {
        // CHANGED: Only multiplication with constants is supported
        start_position = (position->slice == ARGON2_SYNC_POINTS - 1)
                             ? 0
            : (position->slice + 1) /* * instance->segment_length */;
    }

    /* 1.2.6. Computing absolute position */
    // CHANGED: Triggers broken groebner multiplication
    absolute_position = (start_position + relative_position); // %
        //                        instance->lane_length; /* absolute position */
    return absolute_position;
}
