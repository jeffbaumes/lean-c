# tokenize

```c
uint32_t tokenize(const uint8_t *p, uint32_t n, uint32_t *starts, uint32_t *lens, uint32_t cap);
```

Splits the `n` bytes at `p` into tokens. A token is a maximal non-empty run of bytes that are not whitespace, where whitespace is exactly space `0x20`, tab `0x09`, newline `0x0A` and carriage return `0x0D`.

- Returns the total number of tokens in the buffer (even if more than `cap`).
- For the first `min(count, cap)` tokens, in order, writes `starts[k]` (offset of its first byte) and `lens[k]` (its length). Entries `k ≥ min(count, cap)` of `starts` and `lens` are left unchanged. `p` is not modified.
- Example: `"  ab c\n"` (n = 7) has tokens `(2, 2)` and `(5, 1)` and returns 2. With `cap = 1` it still returns 2 but writes only `starts[0] = 2, lens[0] = 2`.
- Preconditions: `p` has `n` readable bytes; `starts` and `lens` each have `cap` writable elements; the three buffers don't overlap.
