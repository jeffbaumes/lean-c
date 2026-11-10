#ifndef CRC32_H
#define CRC32_H
#include <stdint.h>

/* CRC-32/ISO-HDLC (zlib, PNG, Ethernet) of the n bytes at p.
 * Reflected, poly 0xEDB88320, init 0xFFFFFFFF, xorout 0xFFFFFFFF.
 * Precondition: p points to at least n readable bytes (p may be NULL if n == 0). */
uint32_t crc32(const uint8_t *p, uint32_t n);

#endif
