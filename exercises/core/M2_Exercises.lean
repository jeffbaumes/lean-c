/-
Milestone 2 exercises. Each one takes 15 minutes or less.
Run:  lake env lean exercises/core/M2_Exercises.lean      (after `lake build`)

Read docs/m2-walkthrough.md and Examples/M2.lean first.
Solutions: exercises/solutions/M2_Exercises.lean.
-/
import LC
import Examples.M2
open LC Examples.M2

/-! ## M2.1 (✍️ 5 min)
`wp_while` (LC/Logic/Hoare.lean) has three hypotheses: `hcond`, `hbody`, `hexit`.
Write a loop for which `hbody` and `hexit` hold but `hcond` fails. Then say what
would go wrong if the rule omitted `hcond`. -/

/-! ## M2.2 (🔧 5 min): straight-line code is just `simp`
The simp lemmas `wp_seq`, `wp_assign` and the `Eval.lean` lemmas *execute* the code
symbolically. Try `simp [Stmt.block]` and watch it close the goal. Then break it: change the
postcondition to something false and read what `simp` leaves you. -/
example (x y z : Nat) :
    wp (.block ["t" ::= v "a", "a" ::= v "b", "b" ::= v "t"])
      (fun σ => σ.st.get "a" = some (nu32 y) ∧ σ.st.get "b" = some (nu32 x))
      ⟨[("a", nu32 x), ("b", nu32 y), ("t", nu32 z)], []⟩ := by
  sorry

/-! ## M2.3 (🔧 15 min): a function with a branch
Prove `max` correct. Follow the `suffices … Fn.returns_of_wp` pattern from
`sumTo_correct`. After `simp [maxFn, nu32, intBinOp, BitVec.ult, Nat.mod_eq_of_lt ha, …]` you'll
get a disjunction (the two `if` branches): `by_cases h : a < b`, then `left`/`right`.
Note the spec writes `((max a b : Nat) : Int)`. Why does the coercion's position matter? -/
def maxFn : Fn where
  name := "max"; params := [("a", .int .u32), ("b", .int .u32)]; locals := [("r", .int .u32)]
  body := .ite (v "a" <. v "b") ("r" ::= v "b") ("r" ::= v "a")
  ret := .int .u32; result := v "r"

theorem maxFn_correct (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    maxFn.Returns [.u32 a, .u32 b] [] (.u32 ((max a b : Nat) : Int)) [] := by
  sorry

/-! ## M2.4 (🔧 15 min): total correctness says no to `while (true) {}`
First show there is no execution at all. Hint: `generalize hs : Stmt.while … = s at h`,
then `induction h`; most cases are contradicted by `hs`. -/
theorem spin_no_exec (σ σ' : State) : ¬ Exec σ (.while (.lit (.bool true)) .skip) σ' := by
  sorry

theorem spin_no_triple :
    ¬ Triple (fun _ => True) (.while (.lit (.bool true)) .skip) (fun _ => True) := by
  sorry

/-! ## M2.5 (🔧 stretch, 2 × 15 min): count down instead of up
Write `sumDown` (`i = n; s = 0; while (i != 0) { s = s + (uint64_t)i; i = i - 1; }`) and prove
it returns `tri n`. Suggested invariant: `s = tri n - tri i`. You'll need `tri_succ`, and a
fact about `BitVec.ofNat 32 i - 1#32` when `0 < i` (try `BitVec.toNat_sub` plus `BitVec.eq_of_toNat_eq`).
No solution file for this one yet. Bring me your attempt and we'll go through it. -/

/-! ## M2.6 (✍️ 5 min)
`sumTo_correct` (Examples/M2.lean) needs `n < 2 ^ 32`, and `sumTo_exact` adds a second
argument (`tri_lt`). Explain in two sentences why `sumTo_correct` *alone* would be a
misleading thing to put in a README. -/
