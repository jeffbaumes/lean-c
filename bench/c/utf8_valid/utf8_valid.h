#ifndef UTF8_VALID_H
#define UTF8_VALID_H
#include <stdbool.h>
#include <stdint.h>

/* True iff the n bytes at p are well-formed UTF-8 (Unicode 3.9 Table 3-7,
 * RFC 3629). Precondition: p points to at least n readable bytes (p may be
 * NULL when n == 0). */
bool utf8_valid(const uint8_t *p, uint32_t n);

#endif
