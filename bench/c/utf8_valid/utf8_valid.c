#include "utf8_valid.h"

static bool in(uint8_t b, uint8_t lo, uint8_t hi) { return b >= lo && b <= hi; }

bool utf8_valid(const uint8_t *p, uint32_t n)
{
    uint32_t i = 0;
    while (i < n) {
        uint8_t b0 = p[i];
        if (b0 <= 0x7F) { i += 1; continue; }

        uint32_t len;
        uint8_t lo = 0x80, hi = 0xBF;  /* allowed range of the second byte */
        if (in(b0, 0xC2, 0xDF))      { len = 2; }
        else if (b0 == 0xE0)         { len = 3; lo = 0xA0; }
        else if (in(b0, 0xE1, 0xEC)) { len = 3; }
        else if (b0 == 0xED)         { len = 3; hi = 0x9F; }
        else if (in(b0, 0xEE, 0xEF)) { len = 3; }
        else if (b0 == 0xF0)         { len = 4; lo = 0x90; }
        else if (in(b0, 0xF1, 0xF3)) { len = 4; }
        else if (b0 == 0xF4)         { len = 4; hi = 0x8F; }
        else return false;           /* 80..C1, F5..FF */

        if (n - i < len) return false;                 /* truncated */
        if (!in(p[i + 1], lo, hi)) return false;
        for (uint32_t k = 2; k < len; k++)
            if (!in(p[i + k], 0x80, 0xBF)) return false;
        i += len;
    }
    return true;
}
