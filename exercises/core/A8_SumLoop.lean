/-
A8 — Verifying an imperative loop with Lean's VC generator.
Run:  lean exercises/core/A8_SumLoop.lean

`mvcgen` turns a goal about monadic code into verification conditions (VCs),
leaving you to supply the loop invariant. Our own `wp` for LC (Milestone 2)
will work the same way on *deep* ASTs — so pay attention to the shape of the VCs.

Note: Lean 4.35 deprecates the name `mvcgen` in favour of an experimental `vcgen`.
At the time of writing `vcgen` failed on this exact example, so we stay on `mvcgen`.
-/
import Std.Tactic.Do
open Std.Do
set_option linter.deprecated.syntax false

def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n+1] do
    acc := acc + i
  return acc

#eval sumTo 10   -- 55

-- Step 1 (math, no loops): Gauss. Hint: induction; `List.range'_concat`, `List.sum_append`, then `simp`/`grind`.
theorem gauss (n : Nat) : 2 * (List.range' 0 (n+1)).sum = n * (n + 1) := by
  sorry

-- Step 2 (the loop). `xs.prefix` is the list of loop values already processed.
-- Replace the invariant `True` with the right one, then finish with
--   all_goals simp_all
--   rw [← gauss n]; simp at *
-- First, put `all_goals trace_state` after `mvcgen` and READ the three VCs:
--   which is "invariant holds initially", "preserved by one iteration", "implies post"?
theorem sumTo_spec (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  generalize h : sumTo n = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, acc⟩ => ⌜True⌝
  all_goals sorry
