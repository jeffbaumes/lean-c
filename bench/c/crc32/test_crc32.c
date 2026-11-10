#include "crc32.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
#define CHECK_EQ(got, want, what) do { uint32_t g_ = (got), w_ = (want); \
    if (g_ != w_) { fprintf(stderr, "FAIL %s: got 0x%08X want 0x%08X\n", what, g_, w_); failures++; } } while (0)

static uint32_t crcs(const char *s) { return crc32((const uint8_t *)s, (uint32_t)strlen(s)); }

/* Independent reference: table-driven, table built from the non-reflected poly by bit reversal. */
static uint32_t rev32(uint32_t x) { uint32_t r = 0; for (int i = 0; i < 32; i++) { r = (r << 1) | (x & 1); x >>= 1; } return r; }
static uint8_t rev8(uint8_t x) { uint8_t r = 0; for (int i = 0; i < 8; i++) { r = (uint8_t)((r << 1) | (x & 1)); x >>= 1; } return r; }
/* MSB-first CRC with explicit reflection of input/output: a different formulation of the same spec. */
static uint32_t ref_crc(const uint8_t *p, size_t n) {
    static uint32_t table[256]; static int init = 0;
    if (!init) {
        for (uint32_t b = 0; b < 256; b++) {
            uint32_t c = b << 24;
            for (int k = 0; k < 8; k++) c = (c & 0x80000000u) ? (c << 1) ^ 0x04C11DB7u : (c << 1);
            table[b] = c;
        }
        init = 1;
    }
    uint32_t c = 0xFFFFFFFFu;
    for (size_t i = 0; i < n; i++) c = (c << 8) ^ table[((c >> 24) ^ rev8(p[i])) & 0xFF];
    return rev32(c) ^ 0xFFFFFFFFu;
}

int main(void) {
    /* Spec check values */
    CHECK_EQ(crcs("123456789"), 0xCBF43926u, "check value");
    CHECK_EQ(crc32((const uint8_t *)"x", 0), 0u, "n=0");
    CHECK_EQ(crc32(NULL, 0), 0u, "NULL, n=0");

    /* Published vectors (zlib/Python binascii.crc32) */
    CHECK_EQ(crcs("a"), 0xE8B7BE43u, "a");
    CHECK_EQ(crcs("abc"), 0x352441C2u, "abc");
    CHECK_EQ(crcs("The quick brown fox jumps over the lazy dog"), 0x414FA339u, "fox");
    uint8_t z[32]; memset(z, 0, sizeof z);
    CHECK_EQ(crc32(z, 32), 0x190A55ADu, "32 zeros");
    memset(z, 0xFF, sizeof z);
    CHECK_EQ(crc32(z, 32), 0xFF6CAB0Bu, "32 0xFF");
    uint8_t one0 = 0; CHECK_EQ(crc32(&one0, 1), 0xD202EF8Du, "single 0x00");
    uint8_t oneF = 0xFF; CHECK_EQ(crc32(&oneF, 1), 0xFF000000u, "single 0xFF");

    /* Only reads n bytes: the byte after the range must not matter. */
    uint8_t buf2[10] = "123456789"; buf2[9] = 0xAA;
    CHECK_EQ(crc32(buf2, 9), 0xCBF43926u, "ignores trailing byte");

    /* Exact-size heap buffer so ASan catches any over-read. */
    uint8_t *h = malloc(9); memcpy(h, "123456789", 9);
    CHECK_EQ(crc32(h, 9), 0xCBF43926u, "heap exact");
    free(h);

    /* All single bytes and random buffers vs. independent reference. */
    for (int b = 0; b < 256; b++) { uint8_t x = (uint8_t)b; char w[32]; snprintf(w, sizeof w, "byte %d", b); CHECK_EQ(crc32(&x, 1), ref_crc(&x, 1), w); }
    srand(12345);
    enum { MAX = 4096 };
    for (int t = 0; t < 2000; t++) {
        uint32_t n = (uint32_t)(rand() % MAX);
        uint8_t *buf = malloc(n ? n : 1);
        for (uint32_t i = 0; i < n; i++) buf[i] = (uint8_t)rand();
        char w[48]; snprintf(w, sizeof w, "random len %u", n);
        uint32_t c = crc32(buf, n);
        CHECK_EQ(c, ref_crc(buf, n), w);
        /* Residue property: appending the CRC little-endian gives the magic residue. */
        uint8_t *ext = malloc(n + 4); memcpy(ext, buf, n);
        ext[n] = (uint8_t)c; ext[n+1] = (uint8_t)(c >> 8); ext[n+2] = (uint8_t)(c >> 16); ext[n+3] = (uint8_t)(c >> 24);
        CHECK_EQ(crc32(ext, n + 4), 0x2144DF1Cu, "residue");
        /* Single-bit flips always change the CRC. */
        if (n) { uint32_t i = (uint32_t)rand() % n; buf[i] ^= (uint8_t)(1u << (rand() % 8)); if (crc32(buf, n) == c) { fprintf(stderr, "FAIL bit flip undetected\n"); failures++; } }
        free(ext); free(buf);
    }

    /* Larger buffer (1 MiB) */
    uint32_t big = 1u << 20; uint8_t *bb = malloc(big);
    for (uint32_t i = 0; i < big; i++) bb[i] = (uint8_t)(i * 31u + 7u);
    CHECK_EQ(crc32(bb, big), ref_crc(bb, big), "1MiB");
    free(bb);

    if (failures) { fprintf(stderr, "%d failure(s)\n", failures); return 1; }
    printf("all tests passed\n");
    return 0;
}
