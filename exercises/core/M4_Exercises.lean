/-
Milestone 4 exercises. Each one takes 15 minutes or less.
Run:  lake env lean exercises/core/M4_Exercises.lean      (after `lake build`)
Difftest: lake exe lc difftest [cases] [seed] [function]

Read docs/m4-walkthrough.md, LC/Emit/C.lean and generated/examples.c first.
Solutions: exercises/solutions/M4_Exercises.lean.
-/
import LC
import Examples.M4
open LC Examples.M4

/-! ## M4.1 (🔧 10 min): break the printer on purpose
In LC/Emit/C.lean, find the unsigned-narrow branch of `Expr.toC` for binary operators (the one
that casts both operands to `uint32_t`). Replace it with the naive `(({T})(a op b))`. Run
  lake build lc && lake exe lc difftest 200 1 mul16
Which build fails, the sanitised one or -O2? Why does the other one pass? Then restore
the line and re-run. -/

/-! ## M4.2 (✍️ 10 min): stricter than C
In a full `lake exe lc difftest` run, `mul_i16` and `cast_i8` have stuck cases, but the
sanitizers flag *none* of them. Explain why (hint: C11 §6.3.1.1 and §6.3.1.3¶3). Is it a
problem that LC is stricter than C here? Which direction of mismatch would be a problem? -/

/-! ## M4.3 (🔧 15 min): hunt for a printer bug
Write a one-expression function you suspect a naive printer would get wrong. Idea: complement
then shift right on a `u8` (`~a >> 4`). In C, `~a` is computed in `int`, so it's negative.
Use `unFn` from Examples/M4.lean. Check one value with `#guard … .call …`, `#eval` its `.toC`,
then add it to `Examples.M4.stress` and run the difftest on it. -/

/-! ## M4.4 (🔧 15 min, optional): make the output prettier, safely
The printer parenthesises everything, so even `return ((d != 0u) && …);` gets an outer pair.
Pick one readability improvement that can't change meaning (e.g. no outer parens at
statement level). Implement it, then show that `lake exe lc difftest` still passes. -/

/-! ## M4.5 (✍️ 5 min)
What exactly does an `ALL PASS` from the difftest establish, and what does it not? -/

/-! ## M4.6 (🔧 5 min): pin down the identifier check
Add `#guard`s showing that `cValidIdent` rejects every C keyword and reserved names like `_Foo`
and `__x`, and accepts `_x1`. -/
