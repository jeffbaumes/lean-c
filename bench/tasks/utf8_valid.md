# utf8_valid

```c
bool utf8_valid(const uint8_t *p, uint32_t n);
```

Returns `true` iff the `n` bytes at `p` are well-formed UTF-8 (Unicode §3.9, Table 3-7; RFC 3629):

- Each code point is encoded in 1–4 bytes in the shortest possible form (no overlong encodings, so `C0`, `C1`, `F5`–`FF` never appear).
- No surrogates (`U+D800`–`U+DFFF`, i.e. `ED A0..BF ..` is invalid).
- No code points above `U+10FFFF` (`F4 90.. ..` and up are invalid).
- No truncated sequence at the end, and no stray continuation byte.
- The empty buffer is valid.

Precondition: `p` points to at least `n` readable bytes.
