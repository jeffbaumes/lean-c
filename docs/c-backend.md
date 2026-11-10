# The C printer and differential testing

**Status:** done. `lake build` is green, the differential tester reports **ALL PASS**, and the emitted C compiles with `-std=c11 -Wall -Wextra -Werror -pedantic`, including under `-ffreestanding -nostdlib`. This is the first milestone where LC's semantics meets a real C compiler.

## 1. [LC/Emit/C.lean](../LC/Emit/C.lean): the printer

`Fn.toC : Fn → Except String String`. It's about 180 lines, and **it's trusted** (proving it correct is future work). So the rules aim to be obviously correct, not clever:

| Rule | Why |
|---|---|
| Parenthesise everything | no reliance on C precedence |
| Print every expression at its LC type | the printer needs types to choose casts, so a function must type-check first |
| **Narrow unsigned arithmetic goes through `uint32_t`**: `((uint16_t)((uint32_t)a * (uint32_t)b))` | C promotes `uint16_t` to *signed* `int`, so naive `a * b` is UB at 0xFFFF² (assignment A3, case 2). LC means "multiply mod 2¹⁶" |
| Narrow signed arithmetic is computed in `int`, then cast back | exact for 8/16-bit operands, and LC is stuck unless the result fits |
| `_Static_assert(INT_MAX == 2147483647, …)` | the promotion rule assumes 32-bit `int`. That's a TCB assumption, now checked by the compiler |
| Literals: `5u`, `UINT64_C(5)`, `INT32_MIN` | each C literal is itself in range (`-2147483648` isn't a valid `int` literal) |
| Names verbatim, but must be valid and non-reserved | readable output, and no renaming scheme to prove injective. Anything else is refused |
| Headers: `<stdint.h>`, `<stdbool.h>`, `<limits.h>` only | all three are freestanding headers (C11 §4¶6). There are no allocations or libc calls |

The result is [generated/lc_examples.c](../generated/lc_examples.c). It reads like hand-written C, apart from the extra parentheses:

```c
uint64_t array_sum(uint32_t *p, uint32_t n) {
  uint32_t i;
  uint32_t x;
  uint64_t s;
  i = 0u;
  s = UINT64_C(0);
  while (i < n) {
    x = p[i];
    s = (s + ((uint64_t)x));
    i = (i + 1u);
  }
  return s;
}
```

## 2. [Tests/PrinterStress.lean](../Tests/PrinterStress.lean): programs aimed at the printer's weak spots

`mul16`, `add8`, `sub8`, `shl8`, `neg8` and `not16` cover narrow unsigned operations. `mul_i16` and `add_i32` cover signed overflow. `div_i32` and `mod_i32` cover truncating division, including negative operands. `neg_i64` covers `-INT64_MIN`. `lt_i8` is a signed comparison. `cast_u8`, `cast_i8` and `cast_i64` cover conversions. `fnv1a` is a real hash over a byte buffer with a known-answer `#guard`. Together with eight earlier examples, that's 24 functions.

## 3. [Tools/Suite.lean](../Tools/Suite.lean): `lake exe lc difftest [cases] [seed] [fn | --module M]`

1. Random inputs come from a dependency-free xorshift PRNG, biased toward 0, 1, −1, MIN, MAX and small counts.
   - Each pointer gets its own random block, or, with probability ¼, shares a block with another pointer to test aliasing.
2. The **interpreter** labels each input:
   - `ok`: expected output.
   - `stuck`: UB. **Never run as a normal test.**
   - `outOfFuel`: skipped.
3. A C harness reproduces each case: it `malloc`s the blocks, calls the function, and prints the result and the final memory in `Val.toString` format.
4. Two builds of the same harness: **sanitised** `-O1 -fsanitize=undefined,address -fno-sanitize-recover=all`, and **optimised** `-O2`. Outputs are compared line by line.
5. **UB oracle:** up to 20 stuck cases per function run alone in the sanitised binary. "Flagged" means C's sanitizers agree it's UB.

The system compiler comes from `$LC_CC`, default `cc`. Plain `clang` doesn't work, because under `lake exe` Lean's bundled clang, which has no system headers, comes first on `PATH`. That was the first failure.

## 4. What testing found

- **Harness bugs:**
  - A trailing-space format mismatch.
  - Two functions shared the name `sub32`, so one overwrote the other's files. LC now gives `sub32u` its own name. Name collisions in a translation unit are something the printer should reject (the printer now rejects them).
  - One process per case took 9 minutes. Batching OK cases into one run brought it down to about 5.
- **The printer's promotion rule matters, and the tester proves it.** Replacing the `uint32_t` casts with naive `a * b` makes the sanitised build fail on the first edge case: `runtime error: signed integer overflow: 65535 * 65535 cannot be represented in type 'int'`. The **-O2 build passed anyway**, because the optimiser happened to emit a wrapping multiply. Without the sanitised configuration, this bug would ship. (Exercise C.1 reproduces it.)
- **ASan missed a 16-element overread of a 1-element *stack* array.** It returned garbage with exit 0. Moving harness buffers to the heap fixed detection for `array_sum` (20/20 stuck cases flagged).
- **Sanitizer silence isn't absence of UB.** `copy_u8(p, p, 7)` on a 1-byte buffer is out of bounds, but the optimiser deletes the self-copy `x[i] = x[i]` loop, so there's nothing to detect.
- **LC is stricter than C, by design.** `mul_i16` and `cast_i8` have stuck cases that no sanitizer flags. In C those are implementation-defined conversions after promotion, not UB (C11 §6.3.1.3¶3). Stricter is the safe direction: LC only ever proves things about programs C also defines. (Exercise C.2.)

## 5. Proved · tested · trusted

| Proved | Tested | Trusted |
|---|---|---|
| the interpreter, Hoare-logic and separation-logic results | **the printer and the semantics' model of C**, on 2,055 interpreter-defined random cases across 24 functions, each run under sanitisers *and* -O2, on Apple clang 17/macOS x86-64. Also: sanitizers agree with LC about UB in most stuck cases | the printer itself (unproved); the C compiler; the 32-bit `int` assumption (now `_Static_assert`ed); that the tested cases are representative |

The TCB is the same set of components as before. What changed is that two of them, "the semantics matches C" and "the printer is right", now have evidence behind them.

## 6. Results

`nice -n 19 lake exe lc difftest 100 7`: 100 random inputs per function, seed 7. This run used 100 cases rather than 200 because the full run made the machine sluggish.

| | |
|---|---|
| functions | 24, **all PASS** |
| inputs the interpreter accepted (`ok`), compared under both builds | 2,055 |
| inputs with UB (`stuck`), never run as tests | 333 |
| out of fuel (`sum_to` with huge `n`) | 12 |
| stuck inputs replayed under sanitizers | 189, of which **141 flagged** |

Why the other 48 weren't flagged. None of them is a bug; each is a place where LC is stricter than C, or where the optimiser removes the access:

| function | unflagged | reason |
|---|---|---|
| `mul_i16` | 20/20 | C computes in `int` (no overflow). Narrowing back to `int16_t` is implementation-defined, not UB |
| `cast_i8` | 20/20 | the same implementation-defined conversion |
| `shl8` | 6/20 | shift amounts 8–31: LC is stuck (amount ≥ width of `u8`), but C shifts the promoted `uint32_t`, which is defined. Amounts ≥ 32 *are* flagged |
| `copy_u8` | 2/20 | `dst == src` overreads that the optimiser deletes (the self-copy loop is a no-op) |

Every UB that C also considers UB was caught: signed overflow (`sub32`, `add_i32`), division and remainder corner cases, `-INT64_MIN`, and out-of-bounds reads in `array_sum` and `fnv1a`. An earlier run (50 cases, seed 1) gave the same picture.

## Your exercises

[exercises/core/CBackend.lean](../exercises/core/CBackend.lean):

- **C.1:** inject the naive-promotion bug and watch the tester catch it.
- **C.2:** why some UB isn't flagged.
- **C.3:** write your own printer-breaking function.
- **C.4:** a safe readability improvement.
- **C.5:** what PASS means.
- **C.6:** identifier guards.

