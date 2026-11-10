#include "hashmap.h"

static uint32_t hm_home(uint32_t k, uint32_t cap)
{
    return (uint32_t)(k * 2654435761u) & (cap - 1u);
}

/* Probe at most cap slots. With no deletion, the first empty slot on the
 * probe sequence proves k is absent. */
bool hm_put(uint32_t *keys, uint32_t *vals, uint8_t *used, uint32_t cap, uint32_t k, uint32_t v)
{
    uint32_t mask = cap - 1u;
    uint32_t idx = hm_home(k, cap);
    for (uint32_t i = 0; i < cap; i++) {
        if (!used[idx]) {
            keys[idx] = k;
            vals[idx] = v;
            used[idx] = 1;
            return true;
        }
        if (keys[idx] == k) {
            vals[idx] = v;
            return true;
        }
        idx = (idx + 1u) & mask;
    }
    return false;
}

bool hm_get(const uint32_t *keys, const uint32_t *vals, const uint8_t *used, uint32_t cap, uint32_t k, uint32_t *out)
{
    uint32_t mask = cap - 1u;
    uint32_t idx = hm_home(k, cap);
    for (uint32_t i = 0; i < cap; i++) {
        if (!used[idx])
            return false;
        if (keys[idx] == k) {
            *out = vals[idx];
            return true;
        }
        idx = (idx + 1u) & mask;
    }
    return false;
}
