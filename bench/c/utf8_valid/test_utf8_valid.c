#include "utf8_valid.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
static long checks = 0;

/* Independent reference: decode by bit arithmetic, then reject overlong,
 * surrogate and > U+10FFFF values. */
static bool ref_valid(const uint8_t *p, size_t n)
{
    size_t i = 0;
    while (i < n) {
        uint8_t b = p[i];
        size_t len; uint32_t cp;
        if ((b & 0x80) == 0)        { len = 1; cp = b; }
        else if ((b & 0xE0) == 0xC0) { len = 2; cp = b & 0x1F; }
        else if ((b & 0xF0) == 0xE0) { len = 3; cp = b & 0x0F; }
        else if ((b & 0xF8) == 0xF0) { len = 4; cp = b & 0x07; }
        else return false;
        if (n - i < len) return false;
        for (size_t k = 1; k < len; k++) {
            if ((p[i + k] & 0xC0) != 0x80) return false;
            cp = (cp << 6) | (p[i + k] & 0x3F);
        }
        static const uint32_t minv[5] = {0, 0, 0x80, 0x800, 0x10000};
        if (len > 1 && cp < minv[len]) return false;
        if (cp >= 0xD800 && cp <= 0xDFFF) return false;
        if (cp > 0x10FFFF) return false;
        i += len;
    }
    return true;
}

/* Copy into an exactly-sized heap buffer so ASan catches any over-read. */
static bool call(const uint8_t *s, size_t n)
{
    uint8_t *buf = malloc(n ? n : 1);
    if (n) memcpy(buf, s, n);
    bool r = utf8_valid(n ? buf : NULL, (uint32_t)n);
    free(buf);
    return r;
}

static void expect(const char *name, const uint8_t *s, size_t n, bool want)
{
    checks++;
    bool got = call(s, n);
    if (got != want) {
        failures++;
        printf("FAIL %s: got %d want %d bytes:", name, got, want);
        for (size_t i = 0; i < n; i++) printf(" %02X", s[i]);
        printf("\n");
    }
    if (ref_valid(s, n) != want) {
        failures++;
        printf("REF DISAGREES on %s\n", name);
    }
}

#define T(name, want, ...) do { \
    static const uint8_t b_[] = {__VA_ARGS__}; \
    expect(name, b_, sizeof b_, want); } while (0)

static size_t encode(uint32_t cp, uint8_t *o)
{
    if (cp < 0x80) { o[0] = (uint8_t)cp; return 1; }
    if (cp < 0x800) { o[0] = (uint8_t)(0xC0 | cp >> 6); o[1] = (uint8_t)(0x80 | (cp & 0x3F)); return 2; }
    if (cp < 0x10000) { o[0] = (uint8_t)(0xE0 | cp >> 12); o[1] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F)); o[2] = (uint8_t)(0x80 | (cp & 0x3F)); return 3; }
    o[0] = (uint8_t)(0xF0 | cp >> 18); o[1] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
    o[2] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F)); o[3] = (uint8_t)(0x80 | (cp & 0x3F)); return 4;
}

static void check_agree(const uint8_t *s, size_t n)
{
    checks++;
    bool a = utf8_valid(s, (uint32_t)n), r = ref_valid(s, n);
    if (a != r) {
        if (failures++ < 20) {
            printf("MISMATCH impl=%d ref=%d:", a, r);
            for (size_t i = 0; i < n; i++) printf(" %02X", s[i]);
            printf("\n");
        }
    }
}

int main(void)
{
    /* Empty buffer, NULL with n = 0, and non-NULL with n = 0. */
    checks++; if (!utf8_valid(NULL, 0)) { failures++; puts("FAIL NULL,0"); }
    checks++; if (!utf8_valid((const uint8_t *)"\xFF", 0)) { failures++; puts("FAIL n=0 ignores bytes"); }

    /* ASCII */
    T("nul", true, 0x00);
    T("ascii", true, 'h', 'e', 'l', 'l', 'o');
    T("del", true, 0x7F);

    /* Boundaries of each length class (Table 3-7) */
    T("U+0080", true, 0xC2, 0x80);
    T("U+07FF", true, 0xDF, 0xBF);
    T("U+0800", true, 0xE0, 0xA0, 0x80);
    T("U+0FFF", true, 0xE0, 0xBF, 0xBF);
    T("U+1000", true, 0xE1, 0x80, 0x80);
    T("U+CFFF", true, 0xEC, 0xBF, 0xBF);
    T("U+D000", true, 0xED, 0x80, 0x80);
    T("U+D7FF", true, 0xED, 0x9F, 0xBF);
    T("U+E000", true, 0xEE, 0x80, 0x80);
    T("U+FFFD", true, 0xEF, 0xBF, 0xBD);
    T("U+FFFF", true, 0xEF, 0xBF, 0xBF);
    T("U+10000", true, 0xF0, 0x90, 0x80, 0x80);
    T("U+3FFFF", true, 0xF0, 0xBF, 0xBF, 0xBF);
    T("U+40000", true, 0xF1, 0x80, 0x80, 0x80);
    T("U+FFFFF", true, 0xF3, 0xBF, 0xBF, 0xBF);
    T("U+100000", true, 0xF4, 0x80, 0x80, 0x80);
    T("U+10FFFF", true, 0xF4, 0x8F, 0xBF, 0xBF);
    T("mixed", true, 'a', 0xC3, 0xA9, 0xE2, 0x82, 0xAC, 0xF0, 0x9F, 0x98, 0x80, 'z');

    /* Overlong */
    T("C0 80 (overlong NUL)", false, 0xC0, 0x80);
    T("C1 BF", false, 0xC1, 0xBF);
    T("E0 9F BF overlong", false, 0xE0, 0x9F, 0xBF);
    T("E0 80 80 overlong", false, 0xE0, 0x80, 0x80);
    T("F0 8F BF BF overlong", false, 0xF0, 0x8F, 0xBF, 0xBF);
    T("F0 80 80 80 overlong", false, 0xF0, 0x80, 0x80, 0x80);

    /* Surrogates */
    T("U+D800", false, 0xED, 0xA0, 0x80);
    T("U+DBFF", false, 0xED, 0xAF, 0xBF);
    T("U+DC00", false, 0xED, 0xB0, 0x80);
    T("U+DFFF", false, 0xED, 0xBF, 0xBF);
    T("surrogate pair CESU", false, 0xED, 0xA0, 0xBD, 0xED, 0xB8, 0x80);

    /* Above U+10FFFF and illegal lead bytes */
    T("U+110000", false, 0xF4, 0x90, 0x80, 0x80);
    T("F4 BF BF BF", false, 0xF4, 0xBF, 0xBF, 0xBF);
    T("F5", false, 0xF5, 0x80, 0x80, 0x80);
    T("F7 BF BF BF", false, 0xF7, 0xBF, 0xBF, 0xBF);
    T("F8 5-byte", false, 0xF8, 0x88, 0x80, 0x80, 0x80);
    T("FC 6-byte", false, 0xFC, 0x84, 0x80, 0x80, 0x80, 0x80);
    T("FE", false, 0xFE);
    T("FF", false, 0xFF);
    T("lone C0", false, 0xC0);

    /* Stray continuation bytes */
    T("lone 80", false, 0x80);
    T("lone BF", false, 0xBF);
    T("ascii then 80", false, 'a', 0x80);
    T("extra continuation", false, 0xC3, 0xA9, 0xA9);
    T("extra after 4-byte", false, 0xF0, 0x9F, 0x98, 0x80, 0x80);

    /* Truncated */
    T("C3 at end", false, 'a', 0xC3);
    T("E2 82 at end", false, 0xE2, 0x82);
    T("E2 at end", false, 0xE2);
    T("F0 9F 98 at end", false, 0xF0, 0x9F, 0x98);
    T("F0 9F at end", false, 0xF0, 0x9F);
    T("F0 at end", false, 0xF0);
    T("truncated then ascii", false, 0xE2, 0x82, 'a');
    T("lead followed by lead", false, 0xC3, 0xC3, 0xA9);
    T("bad 3rd byte", false, 0xE2, 0x82, 0xC0);
    T("bad 4th byte", false, 0xF0, 0x9F, 0x98, 0x7F);
    T("error after valid", false, 0xE2, 0x82, 0xAC, 0xFF);

    /* Every code point: encoded alone (valid iff not a surrogate), and the
     * whole range concatenated in one buffer. */
    {
        uint8_t *big = malloc(0x110000u * 4), b[4];
        size_t len = 0;
        for (uint32_t cp = 0; cp <= 0x10FFFF; cp++) {
            size_t k = encode(cp, b);
            bool want = !(cp >= 0xD800 && cp <= 0xDFFF);
            checks++;
            if (call(b, k) != want) {
                if (failures++ < 20) printf("FAIL code point U+%04X\n", cp);
            }
            /* every proper prefix of a multi-byte encoding is truncated */
            for (size_t j = 1; j < k; j++) {
                checks++;
                if (call(b, j)) { if (failures++ < 20) printf("FAIL prefix U+%04X len %zu\n", cp, j); }
            }
            if (want) { memcpy(big + len, b, k); len += k; }
        }
        checks++;
        if (!call(big, len)) { failures++; puts("FAIL all scalar values concatenated"); }
        free(big);
    }

    /* Exhaustive agreement with the reference for all strings of length
     * 1..3, and all 4-byte strings with lead byte F0..F4 or C2..EF. */
    {
        uint8_t s[4];
        for (uint32_t a = 0; a < 256; a++) {
            s[0] = (uint8_t)a; check_agree(s, 1);
            for (uint32_t b = 0; b < 256; b++) {
                s[1] = (uint8_t)b; check_agree(s, 2);
                for (uint32_t c = 0; c < 256; c++) {
                    s[2] = (uint8_t)c; check_agree(s, 3);
                }
            }
        }
        for (uint32_t a = 0xC0; a < 0x100; a++)
            for (uint32_t b = 0; b < 256; b++)
                for (uint32_t c = 0; c < 256; c++)
                    for (uint32_t d = 0; d < 256; d += (a >= 0xF0 ? 1 : 17)) {
                        s[0] = (uint8_t)a; s[1] = (uint8_t)b; s[2] = (uint8_t)c; s[3] = (uint8_t)d;
                        check_agree(s, 4);
                    }
    }

    /* Random fuzz biased toward UTF-8-ish bytes, against the reference. */
    {
        static const uint8_t pool[] = {0x00, 0x41, 0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF,
                                       0xC0, 0xC1, 0xC2, 0xDF, 0xE0, 0xE1, 0xEC, 0xED, 0xEE,
                                       0xEF, 0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xFF};
        uint8_t buf[64];
        srand(12345);
        for (int it = 0; it < 2000000; it++) {
            size_t n = (size_t)(rand() % 17);
            for (size_t i = 0; i < n; i++)
                buf[i] = (rand() & 1) ? pool[rand() % sizeof pool] : (uint8_t)rand();
            checks++;
            if (call(buf, n) != ref_valid(buf, n)) {
                if (failures++ < 20) {
                    printf("FUZZ MISMATCH:");
                    for (size_t i = 0; i < n; i++) printf(" %02X", buf[i]);
                    printf("\n");
                }
            }
        }
    }

    printf("%ld checks, %d failures\n", checks, failures);
    return failures ? 1 : 0;
}
