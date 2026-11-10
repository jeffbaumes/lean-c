/* Benchmark cross-check: the unit-tested C (bench/c/) against the verified LC-emitted C, on random inputs.
   lc_crc32 / lc_utf8_valid / lc_base64_encode (+ b64_sym) are the functions from generated/lc_examples.c,
   renamed with an lc_ prefix and compiled as separate files. */
#include <stdint.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
uint32_t crc32(const uint8_t *p, uint32_t n);
uint32_t lc_crc32(uint8_t *p, uint32_t n);
bool utf8_valid(const uint8_t *p, uint32_t n);
bool lc_utf8_valid(uint8_t *p, uint32_t n);
uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out);
uint32_t lc_base64_encode(uint8_t *in, uint32_t n, uint8_t *out);
static uint64_t s = 88172645463325252ull;
static uint32_t rnd(void){ s ^= s<<13; s ^= s>>7; s ^= s<<17; return (uint32_t)s; }
static const uint8_t interesting[] = {0x00,0x41,0x7F,0x80,0x8F,0x90,0x9F,0xA0,0xBF,0xC0,0xC1,0xC2,0xDF,0xE0,0xE1,0xEC,0xED,0xEE,0xEF,0xF0,0xF1,0xF3,0xF4,0xF5,0xFF};
static uint8_t byte(int mode){ return mode ? interesting[rnd()%sizeof interesting] : (uint8_t)rnd(); }
int main(void){
  uint8_t buf[64], o1[100], o2[100]; long bad[3] = {0,0,0};
  for (long it = 0; it < 1000000; it++) {
    uint32_t n = rnd() % 33; int mode = rnd() % 2;
    for (uint32_t i = 0; i < n; i++) buf[i] = byte(mode);
    if (crc32(buf,n) != lc_crc32(buf,n)) bad[0]++;
    if (utf8_valid(buf,n) != lc_utf8_valid(buf,n)) { if (!bad[1]++) { printf("utf8 mismatch n=%u:", n); for (uint32_t i=0;i<n;i++) printf(" %02X", buf[i]); printf("\n"); } }
    memset(o1, 0xAA, sizeof o1); memset(o2, 0xAA, sizeof o2);
    if (base64_encode(buf,n,o1) != lc_base64_encode(buf,n,o2) || memcmp(o1,o2,sizeof o1)) bad[2]++;
  }
  printf("mismatches over 1e6 cases: crc32=%ld utf8_valid=%ld base64_encode=%ld\n", bad[0], bad[1], bad[2]);
  return 0;
}
