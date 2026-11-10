# base64_encode

```c
uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out);
```

Encodes the `n` bytes at `in` as base64 (RFC 4648 §4: alphabet `A–Z a–z 0–9 + /`, `=` padding, no line breaks) into `out`, and returns the number of bytes written, which is exactly `4 * ceil(n / 3)`.

- Writes `out[0 .. 4*ceil(n/3))` and nothing else.
- RFC 4648 test vectors: `""→""`, `"f"→"Zg=="`, `"fo"→"Zm8="`, `"foo"→"Zm9v"`, `"foob"→"Zm9vYg=="`, `"fooba"→"Zm9vYmE="`, `"foobar"→"Zm9vYmFy"`.
- Preconditions: `n ≤ 3221225469` (so the output length fits in `uint32_t`); `in` has `n` readable bytes; `out` has `4*ceil(n/3)` writable bytes; the two buffers don't overlap.
