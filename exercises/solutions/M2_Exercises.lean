-- Solutions to exercises/core/M2_Exercises.lean.  Run: lake env lean exercises/solutions/M2_Exercises.lean
import LC
import Examples.M2
open LC Examples.M2

/-! ## M2.1
Without `hcond`, the guard could be UB in an invariant state, e.g. `while (x / d > 0)` with
`d = 0`. Then neither `whileTrue` nor `whileFalse` applies, so there's no execution, yet `hbody`
and `hexit` would be vacuous (both assume the guard evaluated). The rule would "prove"
a stuck program. -/

/-! ## M2.2 swap through a temporary: pure symbolic execution -/
example (x y z : Nat) :
    wp (.block ["t" ::= v "a", "a" ::= v "b", "b" ::= v "t"])
      (fun σ => σ.st.get "a" = some (nu32 y) ∧ σ.st.get "b" = some (nu32 x))
      ⟨[("a", nu32 x), ("b", nu32 y), ("t", nu32 z)], []⟩ := by
  simp [Stmt.block]

/-! ## M2.3 max -/
def maxFn : Fn where
  name := "max"; params := [("a", .int .u32), ("b", .int .u32)]; locals := [("r", .int .u32)]
  body := .ite (v "a" <. v "b") ("r" ::= v "b") ("r" ::= v "a")
  ret := .int .u32; result := v "r"

theorem maxFn_correct (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    maxFn.Returns [.u32 a, .u32 b] [] (.u32 ((max a b : Nat) : Int)) [] := by
  suffices key : wp maxFn.body (fun σ => ∃ w, maxFn.result.eval σ.st = some w ∧
      w.ty = maxFn.ret ∧ (w = .u32 ((max a b : Nat) : Int) ∧ σ.mem = []))
      ⟨[("a", nu32 a), ("b", nu32 b)], []⟩ by
    obtain ⟨w, m', hw, rfl, rfl⟩ := Fn.returns_of_wp (f := maxFn) (args := [.u32 a, .u32 b])
      (st₀ := [("a", nu32 a), ("b", nu32 b)]) (m := [])
      (post := fun w m' => w = .u32 ((max a b : Nat) : Int) ∧ m' = [])
      (by simp [Fn.initStore, maxFn, Store.empty]; constructor <;> rfl) key
    exact hw
  simp [maxFn, nu32, intBinOp, BitVec.ult, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · left; simp [Nat.max_eq_right (Nat.le_of_lt h)]; exact ⟨h, rfl⟩
  · right; refine ⟨by omega, ?_⟩; simp [Nat.max_eq_left (Nat.le_of_not_lt h)]; rfl

/-! ## M2.4 total correctness rejects `while (true) {}` -/
theorem spin_no_exec (σ σ' : State) : ¬ Exec σ (.while (.lit (.bool true)) .skip) σ' := by
  intro h
  generalize hs : Stmt.while (.lit (.bool true)) .skip = s at h
  induction h with
  | whileTrue _ _ _ _ ihw => exact ihw hs
  | whileFalse hc => cases hs; simp at hc
  | _ => cases hs

theorem spin_no_triple :
    ¬ Triple (fun _ => True) (.while (.lit (.bool true)) .skip) (fun _ => True) := by
  intro h
  obtain ⟨σ', hex, -⟩ := h ⟨[], []⟩ trivial
  exact spin_no_exec _ _ hex
