#include "hashmap.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures = 0;
static long checks = 0;
#define CHECK(c) do { checks++; if (!(c)) { failures++; \
    fprintf(stderr, "%s:%d: CHECK failed: %s\n", __FILE__, __LINE__, #c); \
    if (failures > 20) exit(1); } } while (0)

/* Table with arrays allocated at exactly cap elements so ASan catches OOB. */
typedef struct { uint32_t cap; uint32_t *keys, *vals; uint8_t *used; } table;

static table tnew(uint32_t cap) {
    table t = { cap, malloc(cap * sizeof(uint32_t)), malloc(cap * sizeof(uint32_t)), calloc(cap, 1) };
    /* Garbage in unused key/val slots: must not matter. */
    for (uint32_t i = 0; i < cap; i++) { t.keys[i] = 0xDEADBEEFu ^ i; t.vals[i] = 0xCAFEBABEu + i; }
    return t;
}
static void tfree(table *t) { free(t->keys); free(t->vals); free(t->used); }

static uint32_t home(uint32_t k, uint32_t cap) { return (k * 2654435761u) & (cap - 1); }

/* Finite-map model. */
typedef struct { uint32_t n, cap; uint32_t *k, *v; } model;
static model mnew(uint32_t cap) { model m = { 0, cap, malloc(cap * 4), malloc(cap * 4) }; return m; }
static void mfree(model *m) { free(m->k); free(m->v); }
static int mfind(const model *m, uint32_t k) { for (uint32_t i = 0; i < m->n; i++) if (m->k[i] == k) return (int)i; return -1; }
static bool mput(model *m, uint32_t k, uint32_t v) {
    int i = mfind(m, k);
    if (i >= 0) { m->v[i] = v; return true; }
    if (m->n == m->cap) return false;
    m->k[m->n] = k; m->v[m->n] = v; m->n++; return true;
}
static bool mget(const model *m, uint32_t k, uint32_t *out) {
    int i = mfind(m, k); if (i < 0) return false; *out = m->v[i]; return true;
}

typedef struct { uint32_t k, v; } kv;
static int kvcmp(const void *a, const void *b) {
    const kv *x = a, *y = b;
    if (x->k != y->k) return x->k < y->k ? -1 : 1;
    return x->v < y->v ? -1 : x->v > y->v;
}

/* Structural invariants, O(cap log cap):
 *  - used[] is 0/1;
 *  - the multiset of stored (key, val) pairs equals the model exactly
 *    (so keys are distinct and nothing is lost or stale);
 *  - every slot on the probe path from an entry's home to its slot is used
 *    (the linear-probing layout the spec mandates). */
static void check_invariants(const table *t, const model *m) {
    uint32_t cap = t->cap, cnt = 0;
    kv *a = malloc(cap * sizeof(kv)), *b = malloc((m->n ? m->n : 1) * sizeof(kv));
    for (uint32_t i = 0; i < cap; i++) {
        CHECK(t->used[i] == 0 || t->used[i] == 1);
        if (t->used[i]) { a[cnt].k = t->keys[i]; a[cnt].v = t->vals[i]; cnt++; }
    }
    CHECK(cnt == m->n);
    for (uint32_t i = 0; i < m->n; i++) { b[i].k = m->k[i]; b[i].v = m->v[i]; }
    if (cnt == m->n) {
        qsort(a, cnt, sizeof(kv), kvcmp); qsort(b, cnt, sizeof(kv), kvcmp);
        CHECK(memcmp(a, b, cnt * sizeof(kv)) == 0);
    }
    /* run[i] = number of consecutive used slots ending at i (circular, capped at cap). */
    uint32_t *run = calloc(cap, sizeof(uint32_t));
    if (cnt == cap) { for (uint32_t i = 0; i < cap; i++) run[i] = cap; }
    else {
        uint32_t e = 0; while (t->used[e]) e++;           /* some empty slot */
        uint32_t r = 0;
        for (uint32_t j = 1; j <= cap; j++) { uint32_t i = (e + j) & (cap - 1); r = t->used[i] ? r + 1 : 0; run[i] = r; }
    }
    for (uint32_t i = 0; i < cap; i++) if (t->used[i]) {
        uint32_t dist = (i - home(t->keys[i], cap)) & (cap - 1);
        CHECK(dist < run[i]);
    }
    free(run); free(a); free(b);
}

static void mappend(model *m, uint32_t k, uint32_t v) { m->k[m->n] = k; m->v[m->n] = v; m->n++; }

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint32_t rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (uint32_t)(rng >> 32); }

/* Random keys drawn from a small pool (to force overwrites, misses, and
 * collisions) or the full 32-bit range, plus boundary keys. */
static uint32_t rkey(uint32_t pool) {
    switch (rnd() % 8) {
    case 0: return 0;
    case 1: return UINT32_MAX;
    case 2: return rnd();
    case 3: return (rnd() % pool) * 65536u; /* structured keys: low 16 bits zero */
    default: return rnd() % pool;
    }
}

static void random_trace(uint32_t cap, int ops, uint32_t pool, bool full_check) {
    table t = tnew(cap); model m = mnew(cap);
    for (int op = 0; op < ops; op++) {
        uint32_t k = rkey(pool);
        if (rnd() % 2) {
            uint32_t v = rnd();
            /* snapshot to verify "change nothing" on failure */
            bool exp = mput(&m, k, v);
            uint8_t *u0 = NULL; uint32_t *k0 = NULL, *v0 = NULL;
            if (!exp) { u0 = malloc(cap); k0 = malloc(cap * 4); v0 = malloc(cap * 4);
                memcpy(u0, t.used, cap); memcpy(k0, t.keys, cap * 4); memcpy(v0, t.vals, cap * 4); }
            bool got = hm_put(t.keys, t.vals, t.used, cap, k, v);
            CHECK(got == exp);
            if (!exp) { CHECK(memcmp(u0, t.used, cap) == 0); CHECK(memcmp(k0, t.keys, cap * 4) == 0);
                CHECK(memcmp(v0, t.vals, cap * 4) == 0); free(u0); free(k0); free(v0); }
        } else {
            uint32_t sentinel = rnd(), out = sentinel, mout = sentinel;
            uint8_t *u0 = malloc(cap); memcpy(u0, t.used, cap);
            bool exp = mget(&m, k, &mout);
            bool got = hm_get(t.keys, t.vals, t.used, cap, k, &out);
            CHECK(got == exp);
            CHECK(out == mout); /* unchanged on miss */
            CHECK(memcmp(u0, t.used, cap) == 0);
            free(u0);
        }
        if (full_check || op == ops - 1) check_invariants(&t, &m);
    }
    /* Every model key retrievable at the end. */
    for (uint32_t i = 0; i < m.n; i++) { uint32_t o = 0; CHECK(hm_get(t.keys, t.vals, t.used, cap, m.k[i], &o)); CHECK(o == m.v[i]); }
    tfree(&t); mfree(&m);
}

static void test_cap1(void) {
    table t = tnew(1); uint32_t o = 7;
    CHECK(!hm_get(t.keys, t.vals, t.used, 1, 5, &o)); CHECK(o == 7);
    CHECK(hm_put(t.keys, t.vals, t.used, 1, 5, 50));
    CHECK(hm_get(t.keys, t.vals, t.used, 1, 5, &o)); CHECK(o == 50);
    CHECK(hm_put(t.keys, t.vals, t.used, 1, 5, 51));
    CHECK(!hm_put(t.keys, t.vals, t.used, 1, 6, 60));
    CHECK(!hm_get(t.keys, t.vals, t.used, 1, 6, &o)); CHECK(o == 51 || o == 50);
    CHECK(hm_get(t.keys, t.vals, t.used, 1, 5, &o)); CHECK(o == 51);
    CHECK(t.used[0] == 1 && t.keys[0] == 5 && t.vals[0] == 51);
    tfree(&t);
}

/* Exact placement: keys sharing a home fill consecutive slots, wrapping. */
static void test_layout_and_wrap(void) {
    uint32_t cap = 8;
    /* Find keys whose home is cap-1 so probing must wrap to 0, 1, ... */
    uint32_t ks[4]; int n = 0;
    for (uint32_t k = 0; n < 4; k++) if (home(k, cap) == cap - 1) ks[n++] = k;
    table t = tnew(cap);
    for (int i = 0; i < 4; i++) CHECK(hm_put(t.keys, t.vals, t.used, cap, ks[i], 100 + i));
    CHECK(t.used[7] && t.keys[7] == ks[0]);
    CHECK(t.used[0] && t.keys[0] == ks[1]);
    CHECK(t.used[1] && t.keys[1] == ks[2]);
    CHECK(t.used[2] && t.keys[2] == ks[3]);
    for (int i = 0; i < 4; i++) { uint32_t o; CHECK(hm_get(t.keys, t.vals, t.used, cap, ks[i], &o)); CHECK(o == 100u + i); }
    /* Overwrite a wrapped key: no new slot used. */
    CHECK(hm_put(t.keys, t.vals, t.used, cap, ks[3], 999));
    int cnt = 0; for (uint32_t i = 0; i < cap; i++) cnt += t.used[i];
    CHECK(cnt == 4);
    /* Home slot calculation example: k=1 -> 2654435761 & 7 = 1. */
    CHECK(home(1, cap) == (2654435761u & 7u));
    tfree(&t);
}

/* Fill completely, then: overwrite still works, new keys fail, absent gets
 * terminate (full scan without empty slot). */
static void test_full(uint32_t cap) {
    table t = tnew(cap); model m = mnew(cap);
    for (uint32_t i = 0; i < cap; i++) { uint32_t k = i * 0x10001u + 3; CHECK(hm_put(t.keys, t.vals, t.used, cap, k, i)); mappend(&m, k, i); }
    check_invariants(&t, &m);
    uint32_t o = 12345;
    CHECK(!hm_put(t.keys, t.vals, t.used, cap, 0xFFFFFFF0u, 1));
    CHECK(!hm_get(t.keys, t.vals, t.used, cap, 0xFFFFFFF0u, &o)); CHECK(o == 12345);
    for (uint32_t i = 0; i < cap; i++) { uint32_t k = i * 0x10001u + 3; CHECK(hm_put(t.keys, t.vals, t.used, cap, k, ~i)); m.v[i] = ~i; }
    for (uint32_t i = 0; i < cap; i++) { uint32_t k = i * 0x10001u + 3; CHECK(hm_get(t.keys, t.vals, t.used, cap, k, &o)); CHECK(o == ~i); }
    check_invariants(&t, &m);
    tfree(&t); mfree(&m);
}

/* Stale contents of keys[]/vals[] in unused slots must never be read as
 * entries: fill every key slot with the probed key and check misses, for
 * every cap and with a partially filled table. */
static void test_garbage_keys(void) {
    for (uint32_t cap = 1; cap <= 64; cap <<= 1) {
        for (uint32_t k = 0; k < 64; k++) {
            table t = tnew(cap);
            for (uint32_t i = 0; i < cap; i++) { t.keys[i] = k; t.vals[i] = 9; }
            uint32_t o = 1;
            CHECK(!hm_get(t.keys, t.vals, t.used, cap, k, &o)); CHECK(o == 1);
            /* Occupy the home slot of k with a different key, then miss again. */
            uint32_t other = k + 1000; while (home(other, cap) != home(k, cap)) other++;
            if (cap > 1) {
                CHECK(hm_put(t.keys, t.vals, t.used, cap, other, 7));
                for (uint32_t i = 0; i < cap; i++) if (!t.used[i]) t.keys[i] = k;
                CHECK(!hm_get(t.keys, t.vals, t.used, cap, k, &o)); CHECK(o == 1);
            }
            CHECK(hm_put(t.keys, t.vals, t.used, cap, k, 5));
            int cnt = 0; for (uint32_t i = 0; i < cap; i++) cnt += t.used[i];
            CHECK(cnt == (cap > 1 ? 2 : 1));
            CHECK(hm_get(t.keys, t.vals, t.used, cap, k, &o)); CHECK(o == 5);
            tfree(&t);
        }
    }
}

int main(void) {
    test_cap1();
    test_layout_and_wrap();
    test_garbage_keys();
    for (uint32_t cap = 1; cap <= 65536; cap <<= 1) test_full(cap);
    for (uint32_t cap = 1; cap <= 64; cap <<= 1)
        for (int rep = 0; rep < 200; rep++)
            random_trace(cap, (int)(cap * 4 + 8), cap * 2 + 1, true);
    for (uint32_t cap = 128; cap <= 1024; cap <<= 1)
        for (int rep = 0; rep < 5; rep++)
            random_trace(cap, (int)(cap * 3), cap * 2, cap <= 256);
    random_trace(65536, 20000, 100000, false);
    random_trace(4096, 12000, 5000, false); /* fills to cap, then rejects */
    if (failures) { printf("FAIL: %d of %ld checks\n", failures, checks); return 1; }
    printf("OK: %ld checks\n", checks);
    return 0;
}
