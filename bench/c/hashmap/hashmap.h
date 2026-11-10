#ifndef HASHMAP_H
#define HASHMAP_H
#include <stdint.h>
#include <stdbool.h>

/* Bounded open-addressing map uint32_t -> uint32_t over caller storage.
 * cap: power of two, 1 <= cap <= 2^16. used[i] is 0 (empty) or 1 (full).
 * Linear probing from home = (k * 2654435761u) & (cap - 1). No deletion. */
bool hm_put(uint32_t *keys, uint32_t *vals, uint8_t *used, uint32_t cap, uint32_t k, uint32_t v);
bool hm_get(const uint32_t *keys, const uint32_t *vals, const uint8_t *used, uint32_t cap, uint32_t k, uint32_t *out);

#endif
