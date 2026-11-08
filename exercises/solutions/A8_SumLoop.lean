-- Solution to exercises/core/A8_SumLoop.lean
import Std.Tactic.Do
open Std.Do
set_option linter.deprecated.syntax false

def sumTo (n : Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:n+1] do
    acc := acc + i
  return acc

theorem gauss (n : Nat) : 2 * (List.range' 0 (n+1)).sum = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.range'_concat, List.sum_append]
    simp
    grind

theorem sumTo_spec (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  generalize h : sumTo n = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, acc⟩ => ⌜acc = xs.prefix.sum⌝
  all_goals simp_all
  rw [← gauss n]
  simp at *
