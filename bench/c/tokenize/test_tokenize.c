#include "tokenize.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
#define CHECK(c) do { if (!(c)) { fprintf(stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, #c); failures++; } } while (0)

#define SENT 0xDEADBEEFu

/* Independent reference: classify each byte, a token starts where a
 * non-ws byte follows ws or the buffer start. */
static int ref_ws(uint8_t c) { return strchr(" \t\n\r", c) != NULL && c != 0; }

static uint32_t ref_tokenize(const uint8_t *p, uint32_t n, uint32_t *st, uint32_t *ln, uint32_t maxk) {
    uint32_t k = 0;
    for (uint32_t i = 0; i < n; i++) {
        int in = !ref_ws(p[i]);
        int prev_in = i > 0 && !ref_ws(p[i - 1]);
        if (in && !prev_in) {
            if (k < maxk) { st[k] = i; ln[k] = 0; }
            k++;
        }
        if (in && k - 1 < maxk) ln[k - 1]++;
    }
    return k;
}

/* Runs tokenize with given cap and checks against reference, including
 * that entries beyond min(count,cap) and the input are untouched. */
static void check_against_ref(const uint8_t *p, uint32_t n, uint32_t cap) {
    uint32_t rs[512], rl[512];
    uint32_t rc = ref_tokenize(p, n, rs, rl, 512);
    uint32_t *s = malloc(sizeof(uint32_t) * (cap + 4));
    uint32_t *l = malloc(sizeof(uint32_t) * (cap + 4));
    for (uint32_t i = 0; i < cap + 4; i++) { s[i] = SENT; l[i] = SENT; }
    uint8_t *copy = malloc(n ? n : 1);
    memcpy(copy, p, n);
    uint32_t c = tokenize(p, n, s, l, cap);
    CHECK(c == rc);
    uint32_t w = c < cap ? c : cap;
    for (uint32_t k = 0; k < w; k++) {
        CHECK(s[k] == rs[k]);
        CHECK(l[k] == rl[k]);
    }
    for (uint32_t k = w; k < cap + 4; k++) {
        CHECK(s[k] == SENT);
        CHECK(l[k] == SENT);
    }
    CHECK(memcmp(copy, p, n) == 0);
    free(s); free(l); free(copy);
}

/* Exact-size heap buffers so ASan catches any out-of-bounds access. */
static uint32_t run_exact(const char *str, uint32_t cap, uint32_t *out_s, uint32_t *out_l) {
    uint32_t n = (uint32_t)strlen(str);
    uint8_t *p = malloc(n ? n : 1);
    memcpy(p, str, n);
    uint32_t *s = cap ? malloc(sizeof(uint32_t) * cap) : NULL;
    uint32_t *l = cap ? malloc(sizeof(uint32_t) * cap) : NULL;
    uint32_t c = tokenize(n ? p : NULL, n, s, l, cap);
    uint32_t w = c < cap ? c : cap;
    for (uint32_t k = 0; k < w; k++) { out_s[k] = s[k]; out_l[k] = l[k]; }
    free(p); free(s); free(l);
    return c;
}

static void test_examples(void) {
    uint32_t s[8], l[8];
    CHECK(run_exact("  ab c\n", 8, s, l) == 2);
    CHECK(s[0] == 2 && l[0] == 2 && s[1] == 5 && l[1] == 1);

    uint32_t s1[2] = {SENT, SENT}, l1[2] = {SENT, SENT};
    const uint8_t *ex = (const uint8_t *)"  ab c\n";
    CHECK(tokenize(ex, 7, s1, l1, 1) == 2);
    CHECK(s1[0] == 2 && l1[0] == 2 && s1[1] == SENT && l1[1] == SENT);

    CHECK(run_exact("", 0, s, l) == 0);
    CHECK(run_exact("", 4, s, l) == 0);
    CHECK(run_exact("   \t\r\n", 4, s, l) == 0);
    CHECK(run_exact("x", 1, s, l) == 1 && s[0] == 0 && l[0] == 1);
    CHECK(run_exact("hello", 1, s, l) == 1 && s[0] == 0 && l[0] == 5);
    CHECK(run_exact("a b c d", 0, s, l) == 4);
    CHECK(run_exact("a\tb\rc\nd e", 8, s, l) == 5);
    for (uint32_t k = 0; k < 5; k++) CHECK(s[k] == 2 * k && l[k] == 1);
    CHECK(run_exact("ab  ", 2, s, l) == 1 && s[0] == 0 && l[0] == 2);
    CHECK(run_exact("  ab", 2, s, l) == 1 && s[0] == 2 && l[0] == 2);
}

static void test_nonws_control_bytes(void) {
    /* Only the four bytes count as whitespace: \v, \f, NUL, 0xA0, 0xFF are token bytes. */
    const uint8_t buf[] = {0x0B, 0x0C, 0x20, 0x00, 0x20, 0xA0, 0xFF, 0x85, 0x09, 0x1F};
    uint32_t s[8], l[8];
    CHECK(tokenize(buf, sizeof buf, s, l, 8) == 4);
    CHECK(s[0] == 0 && l[0] == 2);
    CHECK(s[1] == 3 && l[1] == 1);
    CHECK(s[2] == 5 && l[2] == 3);
    CHECK(s[3] == 9 && l[3] == 1);
    /* Exhaustive single byte: whitespace iff one of the four. */
    for (int b = 0; b < 256; b++) {
        uint8_t c = (uint8_t)b;
        int ws = b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D;
        uint32_t s1 = SENT, l1 = SENT;
        CHECK(tokenize(&c, 1, &s1, &l1, 1) == (ws ? 0u : 1u));
        if (!ws) CHECK(s1 == 0 && l1 == 1);
        else CHECK(s1 == SENT && l1 == SENT);
    }
}

static void test_exhaustive_small(void) {
    /* All strings of length <= 10 over {' ', '\t', 'a', '\0'} with every cap 0..6. */
    const uint8_t alpha[] = {' ', '\t', 'a', 0x00};
    uint8_t buf[10];
    for (uint32_t n = 0; n <= 10; n++) {
        uint32_t total = 1;
        for (uint32_t i = 0; i < n; i++) total *= 4;
        for (uint32_t code = 0; code < total; code++) {
            uint32_t x = code;
            for (uint32_t i = 0; i < n; i++) { buf[i] = alpha[x % 4]; x /= 4; }
            for (uint32_t cap = 0; cap <= 6; cap += (n > 8 ? 3 : 1))
                check_against_ref(buf, n, cap);
        }
    }
}

static void test_random(void) {
    srand(12345);
    static uint8_t buf[600];
    for (int iter = 0; iter < 20000; iter++) {
        uint32_t n = (uint32_t)(rand() % 600);
        int mode = rand() % 3;
        for (uint32_t i = 0; i < n; i++) {
            if (mode == 0) buf[i] = (uint8_t)rand();
            else if (mode == 1) buf[i] = " \t\r\nxy"[rand() % 6];
            else buf[i] = (rand() % 8) ? ' ' : (uint8_t)(0x21 + rand() % 90);
        }
        uint32_t cap = (uint32_t)(rand() % 400);
        check_against_ref(buf, n, cap);
    }
}

static void test_large(void) {
    /* Large alternating buffer: count = n/2, near-max density. */
    uint32_t n = 1u << 22;
    uint8_t *p = malloc(n);
    for (uint32_t i = 0; i < n; i++) p[i] = (i % 2) ? ' ' : 'z';
    uint32_t cap = n / 2;
    uint32_t *s = malloc(sizeof(uint32_t) * cap), *l = malloc(sizeof(uint32_t) * cap);
    CHECK(tokenize(p, n, s, l, cap) == n / 2);
    int ok = 1;
    for (uint32_t k = 0; k < cap; k++) ok &= (s[k] == 2 * k && l[k] == 1);
    CHECK(ok);
    /* One giant token. */
    memset(p, 'q', n);
    CHECK(tokenize(p, n, s, l, 1) == 1 && s[0] == 0 && l[0] == n);
    free(p); free(s); free(l);
}

int main(void) {
    test_examples();
    test_nonws_control_bytes();
    test_exhaustive_small();
    test_random();
    test_large();
    if (failures) { fprintf(stderr, "%d failures\n", failures); return 1; }
    printf("all tests passed\n");
    return 0;
}
