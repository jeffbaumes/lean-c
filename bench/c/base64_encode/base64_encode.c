#include "base64_encode.h"

static const uint8_t b64_alphabet[64] = {
    'A','B','C','D','E','F','G','H','I','J','K','L','M','N','O','P',
    'Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f',
    'g','h','i','j','k','l','m','n','o','p','q','r','s','t','u','v',
    'w','x','y','z','0','1','2','3','4','5','6','7','8','9','+','/'
};

uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out)
{
    uint32_t full = n / 3u;      /* number of complete 3-byte groups */
    uint32_t rem = n % 3u;       /* 0, 1 or 2 trailing bytes */
    uint32_t i = 0, o = 0;

    for (uint32_t g = 0; g < full; g++) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i + 1] << 8) | (uint32_t)in[i + 2];
        out[o]     = b64_alphabet[(v >> 18) & 0x3Fu];
        out[o + 1] = b64_alphabet[(v >> 12) & 0x3Fu];
        out[o + 2] = b64_alphabet[(v >> 6) & 0x3Fu];
        out[o + 3] = b64_alphabet[v & 0x3Fu];
        i += 3u;
        o += 4u;
    }

    if (rem == 1u) {
        uint32_t v = (uint32_t)in[i] << 16;
        out[o]     = b64_alphabet[(v >> 18) & 0x3Fu];
        out[o + 1] = b64_alphabet[(v >> 12) & 0x3Fu];
        out[o + 2] = '=';
        out[o + 3] = '=';
        o += 4u;
    } else if (rem == 2u) {
        uint32_t v = ((uint32_t)in[i] << 16) | ((uint32_t)in[i + 1] << 8);
        out[o]     = b64_alphabet[(v >> 18) & 0x3Fu];
        out[o + 1] = b64_alphabet[(v >> 12) & 0x3Fu];
        out[o + 2] = b64_alphabet[(v >> 6) & 0x3Fu];
        out[o + 3] = '=';
        o += 4u;
    }
    return o;
}
