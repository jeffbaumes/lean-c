# hashmap (bounded, open addressing, over caller storage)

```c
bool hm_put(uint32_t *keys, uint32_t *vals, uint8_t *used, uint32_t cap, uint32_t k, uint32_t v);
bool hm_get(const uint32_t *keys, const uint32_t *vals, const uint8_t *used, uint32_t cap, uint32_t k, uint32_t *out);
```

A map from `uint32_t` keys to `uint32_t` values, stored in three caller-owned arrays of length `cap`: `keys`, `vals`, and `used` (`used[i]` is 0 for an empty slot, 1 for a full one). There is no deletion. An empty map is any table with `used` all zero.

- Layout: `cap` is a power of two, `1 ≤ cap ≤ 2^16`. Home slot of `k` is `(k * 2654435761u) & (cap - 1)` (multiplication wraps mod 2^32). Collisions use linear probing: home, home+1, … wrapping mod `cap`.
- `hm_put`: if `k` is already in the map, replace its value and return `true`. Otherwise, if there is a free slot, insert `(k, v)` and return `true`. Otherwise (the table is full and `k` is absent) return `false` and change nothing.
- `hm_get`: if `k` is in the map, set `*out` to its value and return `true`. Otherwise return `false` and leave `*out` unchanged. It does not modify the table.
- Required correctness: starting from an empty table, after any sequence of `hm_put`/`hm_get` calls, each call's result (and `*out`) agrees with a plain finite-map model (insert-or-overwrite, bounded by `cap` distinct keys).
- Preconditions: the three arrays have `cap` elements each; `out` and the arrays don't overlap.
