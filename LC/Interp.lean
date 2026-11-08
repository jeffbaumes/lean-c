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
(`exercises/core/M1_Exercises.lean`).

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
def run : Nat → State → Stmt → Result State
  | 0, _, _ => .outOfFuel
  | _ + 1, σ, .skip => .ok σ
  | _ + 1, ⟨st, m⟩, .assign x e =>
    match e.eval st with
    | some v => .ok ⟨st.set x v, m⟩
    | none => .stuck
  | n + 1, σ, .seq s₁ s₂ =>
    match run n σ s₁ with
    | .ok σ₁ => run n σ₁ s₂
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel
  | n + 1, σ, .ite c s₁ s₂ =>
    match c.eval σ.st with
    | some (.bool true) => run n σ s₁
    | some (.bool false) => run n σ s₂
    | _ => .stuck
  | n + 1, σ, .while c b =>
    match c.eval σ.st with
    | some (.bool true) =>
      match run n σ b with
      | .ok σ₁ => run n σ₁ (.while c b)
      | .stuck => .stuck
      | .outOfFuel => .outOfFuel
    | some (.bool false) => .ok σ
    | _ => .stuck
  | _ + 1, ⟨st, m⟩, .load x p i =>
    match Expr.evalAddr st p i with
    | some (t, b, k) =>
      match m.read b k with
      | some v => if v.ty = .int t then .ok ⟨st.set x v, m⟩ else .stuck
      | none => .stuck
    | none => .stuck
  | _ + 1, ⟨st, m⟩, .store p i e =>
    match Expr.evalAddr st p i, e.eval st with
    | some (t, b, k), some v =>
      if v.ty = .int t then
        match m.write b k v with
        | some m' => .ok ⟨st, m'⟩
        | none => .stuck
      else .stuck
    | _, _ => .stuck

/-! ## Soundness of successful runs -/

theorem run_sound {n : Nat} {σ σ' : State} {s : Stmt} :
    run n σ s = .ok σ' → Exec σ s σ' := by
  induction n generalizing σ σ' s with
  | zero => simp [run]
  | succ n ih =>
    cases s with
    | skip => simp only [run, Result.ok.injEq]; rintro rfl; exact .skip
    | assign x e =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next v hv => simp only [Result.ok.injEq]; rintro rfl; exact .assign hv
      · simp
    | seq s₁ s₂ =>
      simp only [run]; split
      · next σ₁ h₁ => intro h₂; exact .seq (ih h₁) (ih h₂)
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
        · simp
        · simp
      · next hc => simp only [Result.ok.injEq]; rintro rfl; exact .whileFalse hc
      · simp
    | load x p i =>
      obtain ⟨st, m⟩ := σ
      simp only [run]; split
      · next t b k ha =>
        split
        · next v hv =>
          split
          · next hty => simp only [Result.ok.injEq]; rintro rfl; exact .load ha hv hty
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
          · next m' hw => simp only [Result.ok.injEq]; rintro rfl; exact .store ha he hty hw
          · simp
        · simp
      · simp

/-! ## Determinism

LC has no non-determinism: unspecified evaluation order is ruled out by pure
expressions (design §2). Determinism is what makes "the interpreter got stuck"
mean "*every* execution gets stuck". CompCert's analogue is
`Clight.semantics_determinate`. -/

theorem Exec.det {σ σ₁ σ₂ : State} {s : Stmt} (h₁ : Exec σ s σ₁) (h₂ : Exec σ s σ₂) :
    σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ with
  | skip => cases h₂; rfl
  | assign hv => cases h₂; simp_all
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂₁ h₂₂ => cases ih₁ h₂₁; exact ih₂ h₂₂
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
    | whileTrue _ hb hw => cases ihb hb; exact ihw hw
    | whileFalse hc' => simp_all
  | whileFalse hc =>
    cases h₂ with
    | whileTrue hc' _ _ => simp_all
    | whileFalse _ => rfl
  | load ha hv _ =>
    cases h₂ with
    | load ha' hv' _ => simp_all
  | store ha he _ hw =>
    cases h₂ with
    | store ha' he' _ hw' =>
      rw [ha] at ha'; cases ha'; rw [he] at he'; cases he'; rw [hw] at hw'; cases hw'; rfl

/-! ## Soundness of stuck runs -/

theorem run_stuck_sound {n : Nat} {σ : State} {s : Stmt} :
    run n σ s = .stuck → ∀ σ', ¬ Exec σ s σ' := by
  induction n generalizing σ s with
  | zero => simp [run]
  | succ n ih =>
    intro hrun σ' hex
    cases s with
    | skip => simp [run] at hrun
    | assign x e =>
      cases hex with
      | assign hv => simp [run, hv] at hrun
    | seq s₁ s₂ =>
      simp only [run] at hrun
      cases hex with
      | seq h₁ h₂ =>
        split at hrun
        · next σ₁ hr₁ => cases (run_sound hr₁).det h₁; exact ih hrun _ h₂
        · next hr₁ => exact ih hr₁ _ h₁
        · simp at hrun
    | ite c s₁ s₂ =>
      simp only [run] at hrun
      split at hrun
      · next hc =>
        cases hex with
        | iteTrue _ h => exact ih hrun _ h
        | iteFalse hc' _ => simp_all
      · next hc =>
        cases hex with
        | iteTrue hc' _ => simp_all
        | iteFalse _ h => exact ih hrun _ h
      · next hc₁ hc₂ => cases hex <;> simp_all
    | «while» c b =>
      simp only [run] at hrun
      split at hrun
      · next hc =>
        cases hex with
        | whileTrue _ hb hw =>
          split at hrun
          · next σ₁ hr => cases (run_sound hr).det hb; exact ih hrun _ hw
          · next hr => exact ih hr _ hb
          · simp at hrun
        | whileFalse hc' => simp_all
      · simp at hrun
      · next hc₁ hc₂ => cases hex <;> simp_all
    | load x p i =>
      cases hex with
      | load ha hv hty => simp [run, ha, hv, hty] at hrun
    | store p i e =>
      cases hex with
      | store ha he hty hw => simp [run, ha, he, hty, hw] at hrun

/-! ## Calling a function -/

/-- Call `f` with arguments `args` and initial memory `m`. -/
def Fn.callMem (f : Fn) (args : List Val) (m : Mem) (fuel : Nat := 100000) : Result (Val × Mem) :=
  match f.initStore args with
  | none => .stuck
  | some st₀ =>
    match run fuel ⟨st₀, m⟩ f.body with
    | .ok σ₁ =>
      match f.result.eval σ₁.st with
      | some v => if v.ty = f.ret then .ok (v, σ₁.mem) else .stuck
      | none => .stuck
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel

theorem Fn.callMem_sound {f : Fn} {args : List Val} {m : Mem} {fuel : Nat} {v : Val} {m' : Mem} :
    f.callMem args m fuel = .ok (v, m') → f.Returns args m v m' := by
  unfold Fn.callMem
  split
  · simp
  · next st₀ h₀ =>
    split
    · next σ₁ h₁ =>
      split
      · next v' hv =>
        split
        · next hty =>
          simp only [Result.ok.injEq, Prod.mk.injEq]; rintro ⟨rfl, rfl⟩
          exact ⟨st₀, σ₁.st, h₀, run_sound h₁, hv, hty⟩
        · simp
      · simp
    · simp
    · simp

/-- Call a function that uses no memory (all M1/M2 examples). -/
def Fn.call (f : Fn) (args : List Val) (fuel : Nat := 100000) : Result Val :=
  match f.callMem args [] fuel with
  | .ok (v, _) => .ok v
  | .stuck => .stuck
  | .outOfFuel => .outOfFuel

theorem Fn.call_sound {f : Fn} {args : List Val} {fuel : Nat} {v : Val} :
    f.call args fuel = .ok v → ∃ m', f.Returns args [] v m' := by
  unfold Fn.call; split
  · next v' m' h => simp only [Result.ok.injEq]; rintro rfl; exact ⟨m', Fn.callMem_sound h⟩
  · simp
  · simp

end LC
