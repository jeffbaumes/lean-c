import LC.Semantics

/-!
# A fuel-bounded interpreter, proved against the semantics

`run` is the executable twin of `Exec`. Two theorems tie them together:

* `run_sound`: if `run` returns `.ok σ'`, then `Exec σ s σ'` holds. Any successful
  run is a *proof* of an execution.
* `run_stuck_sound`: if `run` returns `.stuck`, then **no** execution exists.
  When the interpreter reports UB, the semantics agrees.

`outOfFuel` is the only uninformative answer. Completeness ("if `Exec σ s σ'`,
some fuel makes `run` succeed") is left as an exercise
(`exercises/core/Semantics.lean`).

Precedent: Certora's Lean Clight proves `doStep_sound` for its interpreter. CompCert has
no executable Clight semantics at all.
-/

namespace LC

inductive Result (α : Type) where
  | ok (a : α)
  | stuck
  | outOfFuel
deriving DecidableEq, Repr, Inhabited

/-- Every recursive call consumes one unit of fuel, so `run` is structurally
recursive and Lean accepts it without a termination proof. -/
def run (P : Program) : Nat → State → Stmt → Result (Outcome × State)
  | 0, _, _ => .outOfFuel
  | _ + 1, σ, .skip => .ok (.normal, σ)
  | _ + 1, ⟨st, m⟩, .assign x e =>
    match e.eval st with
    | some v => .ok (.normal, ⟨st.set x v, m⟩)
    | none => .stuck
  | n + 1, σ, .seq s₁ s₂ =>
    match run P n σ s₁ with
    | .ok (.normal, σ₁) => run P n σ₁ s₂
    | .ok (o, σ₁) => .ok (o, σ₁)
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel
  | n + 1, σ, .ite c s₁ s₂ =>
    match c.eval σ.st with
    | some (.bool true) => run P n σ s₁
    | some (.bool false) => run P n σ s₂
    | _ => .stuck
  | n + 1, σ, .while c b =>
    match c.eval σ.st with
    | some (.bool true) =>
      match run P n σ b with
      | .ok (.normal, σ₁) => run P n σ₁ (.while c b)
      | .ok (.brk, σ₁) => .ok (.normal, σ₁)
      | .ok (.ret v, σ₁) => .ok (.ret v, σ₁)
      | .stuck => .stuck
      | .outOfFuel => .outOfFuel
    | some (.bool false) => .ok (.normal, σ)
    | _ => .stuck
  | _ + 1, ⟨st, m⟩, .load x p i =>
    match Expr.evalAddr st p i with
    | some (t, b, k) =>
      match m.read b k with
      | some v => if v.ty = .int t then .ok (.normal, ⟨st.set x v, m⟩) else .stuck
      | none => .stuck
    | none => .stuck
  | _ + 1, ⟨st, m⟩, .store p i e =>
    match Expr.evalAddr st p i, e.eval st with
    | some (t, b, k), some v =>
      if v.ty = .int t then
        match m.write b k v with
        | some m' => .ok (.normal, ⟨st, m'⟩)
        | none => .stuck
      else .stuck
    | _, _ => .stuck
  | _ + 1, σ, .brk => .ok (.brk, σ)
  | _ + 1, σ, .ret e =>
    match e.eval σ.st with
    | some v => .ok (.ret v, σ)
    | none => .stuck
  | n + 1, ⟨st, m⟩, .call x f args =>
    match P.find? f, Expr.evalList st args with
    | some g, some vs =>
      match g.initStore vs with
      | some st₀ =>
        match run P n ⟨st₀, m⟩ g.body with
        | .ok (o, σ₁) =>
          match g.finish o σ₁.st with
          | some v => .ok (.normal, ⟨st.setOpt x v, σ₁.mem⟩)
          | none => .stuck
        | .stuck => .stuck
        | .outOfFuel => .outOfFuel
      | none => .stuck
    | _, _ => .stuck

/-! ## Soundness of successful runs -/

theorem run_sound {P : Program} {n : Nat} {σ σ' : State} {s : Stmt} {o : Outcome} :
    run P n σ s = .ok (o, σ') → Exec P σ s o σ' := by
  induction n generalizing σ σ' s o with
  | zero => simp [run]
  | succ n ih =>
    cases s with
    | skip => simp only [run, Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .skip
    | assign x e =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next v hv => simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .assign hv
      · simp
    | seq s₁ s₂ =>
      simp only [run]; split
      · next σ₁ h₁ => intro h₂; exact .seq (ih h₁) (ih h₂)
      · next o₁ σ₁ hne hr =>
        simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩
        exact .seqAbrupt (ih hr) hne
      · simp
      · simp
    | ite c s₁ s₂ =>
      simp only [run]; split
      · next hc => intro h; exact .iteTrue hc (ih h)
      · next hc => intro h; exact .iteFalse hc (ih h)
      · simp
    | «while» c b =>
      simp only [run]; split
      · next hc =>
        split
        · next σ₁ hb => intro hw; exact .whileTrue hc (ih hb) (ih hw)
        · next σ₁ hb =>
          simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .whileBreak hc (ih hb)
        · next v σ₁ hb =>
          simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .whileRet hc (ih hb)
        · simp
        · simp
      · next hc => simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .whileFalse hc
      · simp
    | load x p i =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next t b k ha =>
        split
        · next v hv =>
          split
          · next hty =>
            simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .load ha hv hty
          · simp
        · simp
      · simp
    | store p i e =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next t b k v ha he =>
        split
        · next hty =>
          split
          · next m' hw =>
            simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .store ha he hty hw
          · simp
        · simp
      · simp
    | brk => simp only [run, Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .brk
    | ret e =>
      simp only [run]; split
      · next v hv => simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩; exact .ret hv
      · simp
    | call x f args =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next g vs hg hvs =>
        split
        · next st₀ h₀ =>
          split
          · next o₁ σ₁ hb =>
            split
            · next v hv =>
              simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩
              exact .call hg hvs h₀ (ih hb) hv
            · simp
          · simp
          · simp
        · simp
      · simp

/-! ## Determinism

LC has no non-determinism: unspecified evaluation order is ruled out by pure
expressions (design §2). Determinism is what makes "the interpreter got stuck"
mean "*every* execution gets stuck". CompCert's analogue is
`Clight.semantics_determinate`. -/

theorem Exec.det {P : Program} {σ σ₁ σ₂ : State} {s : Stmt} {o₁ o₂ : Outcome}
    (h₁ : Exec P σ s o₁ σ₁) (h₂ : Exec P σ s o₂ σ₂) : o₁ = o₂ ∧ σ₁ = σ₂ := by
  induction h₁ generalizing o₂ σ₂ with
  | skip => cases h₂; exact ⟨rfl, rfl⟩
  | assign hv => cases h₂; simp_all
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ => obtain ⟨-, rfl⟩ := ih₁ h₂₁; exact ih₂ h₂₂
    | seqAbrupt h₂₁ hn => exact absurd (ih₁ h₂₁).1.symm hn
  | seqAbrupt _ hn ih =>
    cases h₂ with
    | seq h₂₁ _ => exact absurd (ih h₂₁).1 hn
    | seqAbrupt h₂₁ _ => exact ih h₂₁
  | iteTrue hc _ ih =>
    cases h₂ with
    | iteTrue _ h => exact ih h
    | iteFalse hc' _ => simp_all
  | iteFalse hc _ ih =>
    cases h₂ with
    | iteTrue hc' _ => simp_all
    | iteFalse _ h => exact ih h
  | whileTrue hc _ _ ihb ihw =>
    cases h₂ with
    | whileTrue _ hb hw => obtain ⟨-, rfl⟩ := ihb hb; exact ihw hw
    | whileBreak _ hb => exact absurd (ihb hb).1 (by simp)
    | whileRet _ hb => exact absurd (ihb hb).1 (by simp)
    | whileFalse hc' => simp_all
  | whileBreak hc _ ih =>
    cases h₂ with
    | whileTrue _ hb _ => exact absurd (ih hb).1 (by simp)
    | whileBreak _ hb => exact ⟨rfl, (ih hb).2⟩
    | whileRet _ hb => exact absurd (ih hb).1 (by simp)
    | whileFalse hc' => simp_all
  | whileRet hc _ ih =>
    cases h₂ with
    | whileTrue _ hb _ => exact absurd (ih hb).1 (by simp)
    | whileBreak _ hb => exact absurd (ih hb).1 (by simp)
    | whileRet _ hb => exact ih hb
    | whileFalse hc' => simp_all
  | whileFalse hc =>
    cases h₂ with
    | whileTrue hc' _ _ => simp_all
    | whileBreak hc' _ => simp_all
    | whileRet hc' _ => simp_all
    | whileFalse _ => exact ⟨rfl, rfl⟩
  | load ha hv _ =>
    cases h₂ with
    | load ha' hv' _ => simp_all
  | store ha he _ hw =>
    cases h₂ with
    | store ha' he' _ hw' =>
      rw [ha] at ha'; cases ha'; rw [he] at he'; cases he'; rw [hw] at hw'; cases hw'
      exact ⟨rfl, rfl⟩
  | brk => cases h₂; exact ⟨rfl, rfl⟩
  | ret hv => cases h₂; simp_all
  | call hg hvs h₀ _ hfin ih =>
    cases h₂ with
    | call hg' hvs' h₀' hb' hfin' =>
      rw [hg] at hg'; cases hg'; rw [hvs] at hvs'; cases hvs'; rw [h₀] at h₀'; cases h₀'
      obtain ⟨rfl, rfl⟩ := ih hb'
      rw [hfin] at hfin'; cases hfin'; exact ⟨rfl, rfl⟩

/-! ## Soundness of stuck runs -/

theorem run_stuck_sound {P : Program} {n : Nat} {σ : State} {s : Stmt} :
    run P n σ s = .stuck → ∀ o σ', ¬ Exec P σ s o σ' := by
  induction n generalizing σ s with
  | zero => simp [run]
  | succ n ih =>
    intro hrun o σ' hex
    cases s with
    | skip => simp [run] at hrun
    | assign x e => cases hex with | assign hv => simp [run, hv] at hrun
    | seq s₁ s₂ =>
      simp only [run] at hrun
      split at hrun
      · next σ₁ hr₁ =>
        cases hex with
        | seq h₁ h₂ => obtain ⟨-, rfl⟩ := (run_sound hr₁).det h₁; exact ih hrun _ _ h₂
        | seqAbrupt h₁ hn => exact hn ((run_sound hr₁).det h₁).1.symm
      · simp at hrun
      · next hr₁ =>
        cases hex with
        | seq h₁ _ => exact ih hr₁ _ _ h₁
        | seqAbrupt h₁ _ => exact ih hr₁ _ _ h₁
      · simp at hrun
    | ite c s₁ s₂ =>
      simp only [run] at hrun
      split at hrun
      · next hc =>
        cases hex with
        | iteTrue _ h => exact ih hrun _ _ h
        | iteFalse hc' _ => simp_all
      · next hc =>
        cases hex with
        | iteTrue hc' _ => simp_all
        | iteFalse _ h => exact ih hrun _ _ h
      · next hc₁ hc₂ => cases hex <;> simp_all
    | «while» c b =>
      simp only [run] at hrun
      split at hrun
      · next hc =>
        split at hrun
        · next σ₁ hr =>
          cases hex with
          | whileTrue _ hb hw => obtain ⟨-, rfl⟩ := (run_sound hr).det hb; exact ih hrun _ _ hw
          | whileBreak _ hb => exact absurd ((run_sound hr).det hb).1 (by simp)
          | whileRet _ hb => exact absurd ((run_sound hr).det hb).1 (by simp)
          | whileFalse hc' => simp_all
        · simp at hrun
        · simp at hrun
        · next hr =>
          cases hex with
          | whileTrue _ hb _ => exact ih hr _ _ hb
          | whileBreak _ hb => exact ih hr _ _ hb
          | whileRet _ hb => exact ih hr _ _ hb
          | whileFalse hc' => simp_all
        · simp at hrun
      · simp at hrun
      · next hc₁ hc₂ => cases hex <;> simp_all
    | load x p i => cases hex with | load ha hv hty => simp [run, ha, hv, hty] at hrun
    | store p i e => cases hex with | store ha he hty hw => simp [run, ha, he, hty, hw] at hrun
    | brk => simp [run] at hrun
    | ret e => cases hex with | ret hv => simp [run, hv] at hrun
    | call x f args =>
      cases hex with
      | call hg hvs h₀ hb hfin =>
        simp only [run, hg, hvs, h₀] at hrun
        split at hrun
        · next o₁ σ₁ hr =>
          obtain ⟨rfl, rfl⟩ := (run_sound hr).det hb
          simp [hfin] at hrun
        · next hr => exact ih hr _ _ hb
        · simp at hrun

/-! ## Calling a function -/

/-- Call `f` with arguments `args` and initial memory `m`, inside program `P`
(default: no other functions). -/
def Fn.callMem (f : Fn) (args : List Val) (m : Mem) (fuel : Nat := 100000) (P : Program := []) :
    Result (Val × Mem) :=
  match f.initStore args with
  | none => .stuck
  | some st₀ =>
    match run P fuel ⟨st₀, m⟩ f.body with
    | .ok (o, σ₁) =>
      match f.finish o σ₁.st with
      | some v => .ok (v, σ₁.mem)
      | none => .stuck
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel

theorem Fn.callMem_sound {f : Fn} {args : List Val} {m : Mem} {fuel : Nat} {P : Program} {v : Val}
    {m' : Mem} : f.callMem args m fuel P = .ok (v, m') → f.Returns P args m v m' := by
  unfold Fn.callMem
  split
  · simp
  · next st₀ h₀ =>
    split
    · next o σ₁ h₁ =>
      split
      · next v' hv =>
        simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩
        exact ⟨st₀, o, σ₁, h₀, run_sound h₁, hv, rfl⟩
      · simp
    · simp
    · simp

/-- Call a function that uses no memory. -/
def Fn.call (f : Fn) (args : List Val) (fuel : Nat := 100000) (P : Program := []) : Result Val :=
  match f.callMem args [] fuel P with
  | .ok (v, _) => .ok v
  | .stuck => .stuck
  | .outOfFuel => .outOfFuel

theorem Fn.call_sound {f : Fn} {args : List Val} {fuel : Nat} {P : Program} {v : Val} :
    f.call args fuel P = .ok v → ∃ m', f.Returns P args [] v m' := by
  unfold Fn.call; split
  · next v' m' h => simp only [Result.ok.injEq]; rintro rfl; exact ⟨m', Fn.callMem_sound h⟩
  · simp
  · simp

end LC
