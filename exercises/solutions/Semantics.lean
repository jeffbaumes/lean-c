-- Solutions to exercises/core/Semantics.lean.   Run: lake env lean exercises/solutions/Semantics.lean
import LC
open LC

/-! ## Sem.1 isqrt -/
def isqrt : Fn where
  name := "isqrt"; params := [("n", .int .u32)]; locals := [("r", .int .u64)]
  body := .block [
    "r" ::= .u64 0,
    .while ((v "r" + .u64 1) * (v "r" + .u64 1) <=. .cast .u64 (v "n"))
      ("r" ::= v "r" + .u64 1)
  ]
  ret := .int .u32
  result := .cast .u32 (v "r")

#guard isqrt.typeCheck
#guard isqrt.call [.u32 0] = .ok (.u32 0)
#guard isqrt.call [.u32 15] = .ok (.u32 3)
#guard isqrt.call [.u32 16] = .ok (.u32 4)
#guard isqrt.call [.u32 4294967295] (fuel := 1000000) = .ok (.u32 65535)

/-! ## Sem.2 the wrapping bug -/
def isqrtBad : Fn where
  name := "isqrt_bad"; params := [("n", .int .u32)]; locals := [("r", .int .u32)]
  body := .block [
    "r" ::= .u32 0,
    .while ((v "r" + .u32 1) * (v "r" + .u32 1) <=. v "n") ("r" ::= v "r" + .u32 1)
  ]
  ret := .int .u32
  result := v "r"

-- For n = 2³²−1 *every* u32 value is ≤ n, so the guard `(r+1)*(r+1) <= n` is always true.
-- Once r passes 65535, (r+1)² wraps mod 2³², and the loop never exits. It is an infinite
-- loop with no UB anywhere, because wraparound is *defined*. A "no UB" proof would not
-- catch this; a total-correctness proof (with a variant) would. See the Hoare-logic exercises.
#guard isqrtBad.call [.u32 4294967295] (fuel := 200000) = .outOfFuel
#guard isqrtBad.call [.u32 1000] = .ok (.u32 31)   -- fine on small inputs, which is why tests miss it

/-! ## Sem.3 `while false` is `skip` -/
theorem while_false_iff (σ σ' : State) (s : Stmt) :
    Exec σ (.while (.lit (.bool false)) s) σ' ↔ σ' = σ := by
  constructor
  · intro h; cases h with
    | whileTrue hc _ _ => simp [Expr.eval] at hc
    | whileFalse _ => rfl
  · rintro rfl; exact .whileFalse (by simp [Expr.eval])

/-! ## Sem.4 `skip ;; s` -/
theorem skip_seq_iff (σ σ' : State) (s : Stmt) :
    Exec σ (.seq .skip s) σ' ↔ Exec σ s σ' := by
  constructor
  · intro h; cases h with | seq h₁ h₂ => cases h₁; exact h₂
  · intro h; exact .seq .skip h

/-! ## Sem.5 fuel monotonicity -/
theorem run_mono {n m : Nat} {σ σ' : State} {s : Stmt} (hle : n ≤ m) :
    run n σ s = .ok σ' → run m σ s = .ok σ' := by
  induction n generalizing m σ σ' s with
  | zero => simp [run]
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hle' : n ≤ m := by omega
    cases s with
    | skip => simp [run]
    | assign x e => simp [run]
    | load x p i => simp [run]
    | store p i e => simp [run]
    | seq s₁ s₂ =>
      simp only [run]
      split
      · next σ₁ h₁ => intro h₂; rw [ih hle' h₁]; exact ih hle' h₂
      · simp
      · simp
    | ite c s₁ s₂ =>
      simp only [run]; split
      · exact ih hle'
      · exact ih hle'
      · simp
    | «while» c b =>
      simp only [run]; split
      · split
        · next σ₁ hb => intro hw; rw [ih hle' hb]; exact ih hle' hw
        · simp
        · simp
      · simp
      · simp

/-! ## Sem.6 completeness -/
theorem run_complete {σ σ' : State} {s : Stmt} (h : Exec σ s σ') :
    ∃ n, run n σ s = .ok σ' := by
  induction h with
  | skip => exact ⟨1, rfl⟩
  | assign hv => exact ⟨1, by simp [run, hv]⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁; obtain ⟨n₂, h₂⟩ := ih₂
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [run, run_mono (m := max n₁ n₂) (by omega) h₁]
    exact run_mono (m := max n₁ n₂) (by omega) h₂
  | iteTrue hc _ ih =>
    obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, by simp [run, hc, hn]⟩
  | iteFalse hc _ ih =>
    obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, by simp [run, hc, hn]⟩
  | whileTrue hc _ _ ihb ihw =>
    obtain ⟨n₁, h₁⟩ := ihb; obtain ⟨n₂, h₂⟩ := ihw
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [run, hc, run_mono (m := max n₁ n₂) (by omega) h₁]
    exact run_mono (m := max n₁ n₂) (by omega) h₂
  | whileFalse hc => exact ⟨1, by simp [run, hc]⟩
  | load ha hv hty => exact ⟨1, by simp [run, ha, hv, hty]⟩
  | store ha he hty hw => exact ⟨1, by simp [run, ha, he, hty, hw]⟩

/-! ## Sem.7
Determinism is used in the `seq` and `while` cases: the interpreter ran `s₁` to `σ₁`
and got stuck *from σ₁*, while the hypothetical execution ran `s₁` to some `σₐ`. Only
`Exec.det` lets us conclude `σₐ = σ₁`, so the hypothetical execution also has to
continue from the state where the interpreter got stuck. With non-determinism, the
interpreter's one stuck path would say nothing about the other paths. -/
