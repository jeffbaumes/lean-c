#include "base64_encode.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
#define CHECK(c, ...) do { if (!(c)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } } while (0)

#define CANARY 0xA5u
#define SLACK 16u

/* Independent reference: bit-at-a-time encoding. */
static size_t ref_encode(const uint8_t *in, size_t n, char *out)
{
    const char *A = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t o = 0, nbits = n * 8;
    for (size_t b = 0; b < nbits; b += 6) {
        unsigned v = 0;
        for (size_t k = 0; k < 6; k++) {
            size_t bit = b + k;
            unsigned x = bit < nbits ? (in[bit / 8] >> (7 - bit % 8)) & 1u : 0u;
            v = (v << 1) | x;
        }
        out[o++] = A[v];
    }
    while (o % 4) out[o++] = '=';
    return o;
}

/* Independent decoder for round-trip checks. */
static int dval(int c)
{
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}
static long ref_decode(const uint8_t *s, size_t len, uint8_t *out)
{
    if (len % 4) return -1;
    size_t o = 0;
    for (size_t i = 0; i < len; i += 4) {
        int a = dval(s[i]), b = dval(s[i + 1]);
        int last = (i + 4 == len);
        int c = (last && s[i + 2] == '=') ? -2 : dval(s[i + 2]);
        int d = (last && s[i + 3] == '=') ? -2 : dval(s[i + 3]);
        if (a < 0 || b < 0 || c == -1 || d == -1) return -1;
        if (c == -2 && d != -2) return -1;
        unsigned v = ((unsigned)a << 18) | ((unsigned)b << 12) |
                     ((unsigned)(c < 0 ? 0 : c) << 6) | (unsigned)(d < 0 ? 0 : d);
        out[o++] = (uint8_t)(v >> 16);
        if (c >= 0) out[o++] = (uint8_t)(v >> 8);
        if (d >= 0) out[o++] = (uint8_t)v;
        /* canonical: unused bits must be zero */
        if (c == -2 && (b & 0xF)) return -1;
        if (c >= 0 && d == -2 && (c & 0x3)) return -1;
    }
    return (long)o;
}

static uint32_t expected_len(uint32_t n) { return (uint32_t)(4u * ((n + 2u) / 3u)); }

/* Runs encode with canaries around out; checks everything. */
static void check_one(const uint8_t *in, uint32_t n, const char *want)
{
    uint32_t elen = expected_len(n);
    uint8_t *buf = malloc(elen + 2 * SLACK);
    memset(buf, CANARY, elen + 2 * SLACK);
    uint8_t *out = buf + SLACK;

    /* copy input so we can verify it's not modified */
    uint8_t *inc = malloc(n ? n : 1);
    if (n) memcpy(inc, in, n);

    uint32_t r = base64_encode(inc, n, out);
    CHECK(r == elen, "n=%u: returned %u, want %u", n, r, elen);
    for (uint32_t k = 0; k < SLACK; k++) {
        CHECK(buf[k] == CANARY, "n=%u: underwrite at -%u", n, SLACK - k);
        CHECK(buf[SLACK + elen + k] == CANARY, "n=%u: overwrite at +%u", n, k);
    }
    CHECK(n == 0 || memcmp(inc, in, n) == 0, "n=%u: input modified", n);

    char *ref = malloc(elen + 1);
    size_t rl = ref_encode(in, n, ref);
    CHECK(rl == elen, "n=%u: ref len %zu", n, rl);
    CHECK(memcmp(out, ref, elen) == 0, "n=%u: mismatch vs reference", n);
    if (want) {
        CHECK(strlen(want) == elen && memcmp(out, want, elen) == 0,
              "n=%u: got '%.*s' want '%s'", n, (int)elen, (const char *)out, want);
    }
    /* alphabet and padding structure */
    uint32_t pad = (n % 3 == 0) ? 0 : 3 - n % 3;
    for (uint32_t k = 0; k < elen; k++) {
        if (k >= elen - pad) CHECK(out[k] == '=', "n=%u: expected pad at %u", n, k);
        else CHECK(dval(out[k]) >= 0, "n=%u: bad char 0x%02x at %u", n, out[k], k);
    }
    /* round trip */
    uint8_t *dec = malloc(n + 4);
    long dl = ref_decode(out, elen, dec);
    CHECK(dl == (long)n && (n == 0 || memcmp(dec, in, n) == 0), "n=%u: round trip failed", n);

    free(dec); free(ref); free(inc); free(buf);
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint8_t rnd8(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint8_t)(rng >> 24); }

int main(void)
{
    /* RFC 4648 section 10 vectors */
    static const struct { const char *in, *out; } v[] = {
        {"", ""}, {"f", "Zg=="}, {"fo", "Zm8="}, {"foo", "Zm9v"},
        {"foob", "Zm9vYg=="}, {"fooba", "Zm9vYmE="}, {"foobar", "Zm9vYmFy"},
    };
    for (size_t k = 0; k < sizeof v / sizeof v[0]; k++)
        check_one((const uint8_t *)v[k].in, (uint32_t)strlen(v[k].in), v[k].out);

    /* NULL pointers are fine for n == 0 (nothing read or written) */
    CHECK(base64_encode(NULL, 0, NULL) == 0, "n=0 with NULL");

    /* Edge-value vectors exercising first/last alphabet entries and '+', '/' */
    { uint8_t a[] = {0x00, 0x00, 0x00}; check_one(a, 3, "AAAA"); }
    { uint8_t a[] = {0xFF, 0xFF, 0xFF}; check_one(a, 3, "////"); }
    { uint8_t a[] = {0xFB, 0xEF, 0xBE}; check_one(a, 3, "++++"); }
    { uint8_t a[] = {0xFF}; check_one(a, 1, "/w=="); }
    { uint8_t a[] = {0xFF, 0xFF}; check_one(a, 2, "//8="); }
    { uint8_t a[] = {0x00}; check_one(a, 1, "AA=="); }
    { uint8_t a[] = {0x00, 0x00}; check_one(a, 2, "AAA="); }
    { uint8_t a[] = {0x80}; check_one(a, 1, "gA=="); }
    check_one((const uint8_t *)"Man", 3, "TWFu");
    check_one((const uint8_t *)"Hello, World!", 13, "SGVsbG8sIFdvcmxkIQ==");

    /* Every 1- and 2-byte input (exhaustive tail cases), and all 3-byte
     * values with a stride that hits every 6-bit digit in every position. */
    for (unsigned a = 0; a < 256; a++) {
        uint8_t x[1] = {(uint8_t)a};
        check_one(x, 1, NULL);
        for (unsigned b = 0; b < 256; b++) {
            uint8_t y[2] = {(uint8_t)a, (uint8_t)b};
            check_one(y, 2, NULL);
        }
    }
    for (uint32_t w = 0; w < (1u << 24); w += 4099u) {
        uint8_t z[3] = {(uint8_t)(w >> 16), (uint8_t)(w >> 8), (uint8_t)w};
        check_one(z, 3, NULL);
    }

    /* All 256 byte values in sequence, at every rotation mod 3 */
    {
        uint8_t all[258];
        for (int k = 0; k < 258; k++) all[k] = (uint8_t)k;
        for (uint32_t off = 0; off < 3; off++)
            for (uint32_t len = 250; len <= 255; len++) check_one(all + off, len, NULL);
    }

    /* Random inputs, lengths 0..1000, plus a few larger ones */
    for (uint32_t len = 0; len <= 1000; len++) {
        uint8_t *p = malloc(len ? len : 1);
        for (uint32_t k = 0; k < len; k++) p[k] = rnd8();
        check_one(p, len, NULL);
        free(p);
    }
    {
        uint32_t big[] = {65535, 65536, 65537, 1000000, 1000001, 1000002};
        for (size_t k = 0; k < sizeof big / sizeof big[0]; k++) {
            uint8_t *p = malloc(big[k]);
            for (uint32_t j = 0; j < big[k]; j++) p[j] = rnd8();
            check_one(p, big[k], NULL);
            free(p);
        }
    }

    if (failures) { printf("%d FAILURES\n", failures); return 1; }
    printf("all tests passed\n");
    return 0;
}
