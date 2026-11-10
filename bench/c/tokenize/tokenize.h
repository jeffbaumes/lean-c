#ifndef TOKENIZE_H
#define TOKENIZE_H
#include <stdint.h>

/* Splits p[0..n) into maximal runs of non-whitespace bytes (whitespace is
 * exactly 0x20, 0x09, 0x0A, 0x0D). Returns the total token count; writes
 * starts[k]/lens[k] for the first min(count, cap) tokens only.
 * Preconditions: p has n readable bytes; starts/lens have cap writable
 * elements; buffers don't overlap. */
uint32_t tokenize(const uint8_t *p, uint32_t n, uint32_t *starts, uint32_t *lens, uint32_t cap);

#endif
