-- Solutions to exercises/core/CBackend.lean.  Run: lake env lean exercises/solutions/CBackend.lean
import LC
import Tests.PrinterStress
open LC Tests.PrinterStress

/-! ## C.1
Only the sanitised build fails, with `signed integer overflow: 65535 * 65535 cannot be
represented in type 'int'`. The -O2 build happens to produce the wrapped answer because
the compiler emits a plain 32-bit multiply. That's "works by accident", and a different
compiler, flag, or surrounding code could break it. That's why the tester runs a sanitised build. -/

/-! ## C.2
`mul_i16`: C computes `int16_t * int16_t` in `int` (promotion), where it can't overflow;
converting the too-big result back to `int16_t` is *implementation-defined* (C11 §6.3.1.3¶3),
not UB, so UBSan has nothing to report. `cast_i8` is the same conversion. LC treats both as
stuck, which makes LC *stricter* than C. That's safe: proofs can only ever be about programs
that C also defines. The reverse (LC defining something C leaves undefined) would be the
dangerous direction, and that's what the tester is hunting for. -/

/-! ## C.3 a new stress case -/
def shrNot8 := unFn "shr_not8" .u8 .u8 ((~~~(v "a")) >>> Expr.u8 4)

-- LC: ~0 = 0xFF (as a u8), >> 4 = 0x0F. Naive C `~a >> 4` would shift the *int* -1.
#guard shrNot8.call [.u8 0] = .ok (.u8 15)
#eval match shrNot8.toC with | .ok s => IO.println s | .error e => IO.println e
-- return expression printed: ((uint8_t)((uint32_t)((uint8_t)(~(uint32_t)a)) >> (uint32_t)((uint8_t)4u)))
-- To run it: add `shrNot8` to `Tests.PrinterStress.all`, then `lake exe lc difftest 200 1 shr_not8`.

/-! ## C.5
A PASS means: on these random inputs, with this compiler and platform, the compiled C produced
exactly what the interpreter produced, with no sanitizer reports. It does *not* prove the
printer correct for all programs or inputs, or on other compilers (it relies on the asserted
32-bit `int`). It also says nothing about UB-input behaviour beyond what the sanitizers happen
to catch. Proving it is future work. -/

/-! ## C.6 -/
#guard cKeywords.all (fun k => !cValidIdent k)
#guard !cValidIdent "_Foo" && !cValidIdent "__x" && !cValidIdent "9a" && cValidIdent "_x1"
