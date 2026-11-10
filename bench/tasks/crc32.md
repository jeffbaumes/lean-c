# crc32

```c
uint32_t crc32(const uint8_t *p, uint32_t n);
```

The standard CRC-32 (CRC-32/ISO-HDLC, as used by zlib, PNG and Ethernet) of the `n` bytes at `p`: reflected input and output, polynomial `0xEDB88320` (reflected form of `0x04C11DB7`), initial value `0xFFFFFFFF`, final XOR `0xFFFFFFFF`.

- Compute it bit by bit (no lookup table).
- Check value: `crc32("123456789", 9) == 0xCBF43926`. `crc32(p, 0) == 0`.
- Precondition: `p` points to at least `n` readable bytes.
