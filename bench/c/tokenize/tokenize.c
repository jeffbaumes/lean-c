#include "tokenize.h"
#include <stdbool.h>

static bool is_ws(uint8_t c) {
    return c == 0x20u || c == 0x09u || c == 0x0Au || c == 0x0Du;
}

uint32_t tokenize(const uint8_t *p, uint32_t n, uint32_t *starts, uint32_t *lens, uint32_t cap) {
    uint32_t count = 0; /* at most ceil(n/2) <= 2^31, cannot overflow */
    uint32_t i = 0;
    while (i < n) {
        if (is_ws(p[i])) {
            i++;
            continue;
        }
        uint32_t start = i;
        while (i < n && !is_ws(p[i])) {
            i++;
        }
        if (count < cap) {
            starts[count] = start;
            lens[count] = i - start;
        }
        count++;
    }
    return count;
}
