#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* Each case is chosen by argv[1]. Predict BEFORE running: defined or UB? */
int main(int argc, char **argv) {
  int which = argc > 1 ? atoi(argv[1]) : 0;
  volatile uint32_t u = 0xFFFFFFFFu;
  volatile uint16_t a = 0xFFFF, b = 0xFFFF;
  volatile int32_t s = INT32_MAX;
  volatile uint32_t sh = 32;
  uint8_t buf[4] = {1, 2, 3, 4};
  volatile int i = 4;
  switch (which) {
    case 1: printf("%u\n", u + 1u); break;                 /* unsigned wrap */
    case 2: printf("%u\n", (uint32_t)(a * b)); break;      /* uint16 * uint16 */
    case 3: printf("%d\n", s + 1); break;                  /* signed overflow */
    case 4: printf("%u\n", 1u << sh); break;               /* shift by width */
    case 5: printf("%d\n", buf[i]); break;                 /* one past end */
    case 6: { uint8_t *p = buf + 4; printf("%p\n", (void*)p); } break; /* form one-past ptr */
    case 7: printf("%d\n", INT32_MIN / (volatile int32_t){-1}); break;
  }
  return 0;
}
