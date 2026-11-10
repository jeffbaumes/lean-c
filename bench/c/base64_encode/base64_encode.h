#ifndef BASE64_ENCODE_H
#define BASE64_ENCODE_H
#include <stdint.h>

/* RFC 4648 section 4 base64, '=' padding, no line breaks.
 * Writes exactly 4*ceil(n/3) bytes to out and returns that count.
 * Preconditions: n <= 3221225469; in has n readable bytes; out has
 * 4*ceil(n/3) writable bytes; buffers do not overlap. */
uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out);

#endif
