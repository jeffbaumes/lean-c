#include "crc32.h"

uint32_t crc32(const uint8_t *p, uint32_t n)
{
    uint32_t crc = 0xFFFFFFFFu;
    for (uint32_t i = 0; i < n; i++) {
        crc ^= (uint32_t)p[i];
        for (int k = 0; k < 8; k++) {
            /* mask is all-ones iff the low bit is set; avoids a branch */
            uint32_t mask = (uint32_t)0u - (crc & 1u);
            crc = (crc >> 1) ^ (0xEDB88320u & mask);
        }
    }
    return crc ^ 0xFFFFFFFFu;
}
