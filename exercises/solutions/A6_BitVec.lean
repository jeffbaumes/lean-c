-- Solution to exercises/core/A6_BitVec.lean
/-
A6 — Machine integers as BitVec.               Run:  lean exercises/core/A6_BitVec.lean

`bv_decide` turns a BitVec goal into SAT, runs the bundled CaDiCaL solver and
checks its LRAT certificate inside Lean. When the goal is false it prints a
counterexample — that is often the most useful output.

For each `example`: PREDICT true/false first, then run. Replace `sorry` with
`bv_decide` for the true ones; for the false ones, keep the counterexample in a
comment and fix the statement so it becomes true.
-/
import Std.Tactic.BVDecide

-- 1. Unsigned wraparound is a ring: adding then subtracting round-trips.
example (x y : BitVec 32) : (x + y) - y = x := by bv_decide

-- 2. "x + 1 > x" — a classic assumption in C loop code. (`>` here is unsigned.)
-- FALSE: counterexample x = 255#8 (wraps to 0). Fixed statement:
example (x : BitVec 8) : x ≠ 255 → x + 1 > x := by bv_decide

-- 3. Clearing the lowest set bit.  (x & (x-1)) has strictly fewer bits set …
--    state it as: if x ≠ 0 then (x &&& (x - 1)) < x
example (x : BitVec 16) : x ≠ 0 → (x &&& (x - 1)) < x := by bv_decide

-- 4. Signed overflow detection. This is what our semantics will *require to be false*
--    for every signed `+`. Is this characterisation right?
example (x y : BitVec 32) :
    BitVec.saddOverflow x y = ((x.msb == y.msb) && ((x + y).msb != x.msb)) := by bv_decide

-- 5. The integer-promotion trap (see A3 case 2). LC's semantics for u16 multiply is
--    "multiply in BitVec 16". The printer will emit (uint16_t)((uint32_t)a * (uint32_t)b).
--    Prove those agree: zero-extend to 32, multiply, truncate back to 16.
example (a b : BitVec 16) :
    ((a.zeroExtend 32) * (b.zeroExtend 32)).truncate 16 = a * b := by bv_decide

-- 6. Stretch: midpoint without overflow. Does lo + (hi - lo) / 2 stay between lo and hi?
example (lo hi : BitVec 32) : lo ≤ hi → lo ≤ lo + (hi - lo) / 2 ∧ lo + (hi - lo) / 2 ≤ hi := by
  bv_decide
