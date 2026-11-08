import LC.Interp

/-!
# Hoare logic for LC: total correctness

## The one definition everything rests on

```
wp Pr s Q σ  :=  ∃ σ', Exec Pr σ s .normal σ' ∧ Q σ'
```

"From `σ`, `s` terminates **without UB** in some state satisfying `Q`." LC is
deterministic (`Exec.det`), so "some state" is the same as "the state".

A triple `⦃P⦄ s ⦃Q⦄` is `∀ σ, P σ → wp Pr s Q σ`. Soundness holds **by
construction**: a triple *is* a statement about `Exec`, so there is no separate
"the logic agrees with the semantics" theorem to get wrong. Certora's Lean Clight
logic is defined the same way (its LEAN.md §6.1), and so is Bedrock2's.

The proof rules are then *theorems* about `wp`:

| C construct | rule | file location |
|---|---|---|
| `skip` | `wp_skip` | simp |
| `x = e` | `wp_assign`: `e` must evaluate (no UB!) | simp |
| `s₁; s₂` | `wp_seq` | simp |
| `if` | `wp_ite`: the condition must evaluate | simp |
| `while` | `wp_while`: invariant `I` and variant `μ` (a `Nat` that decreases) | apply by hand |

The simp rules turn `wp` of straight-line code into ordinary Lean goals: **symbolic
execution by rewriting**. Loops need you to supply `I` and `μ`, exactly as in
assignments A7 and A8.

Compare *Concrete Semantics* §12.2–12.5. There the logic is defined first and
proved sound afterwards; we define it semantically and derive the rules. VST and
Iris also take the semantic route.
-/

namespace LC

/-- Assertions are predicates on states (a *shallow* embedding of the assertion
language, while programs stay deep). A state is a store plus a memory;
`LC/Logic/Sep.lean` adds a separation logic for the memory part. -/
abbrev Assertion := State → Prop

/-- Total-correctness weakest precondition. -/
def wp (P : Program) (s : Stmt) (Q : Assertion) : Assertion :=
  fun σ => ∃ σ', Exec P σ s .normal σ' ∧ Q σ'

/-- `⦃P⦄ s ⦃Q⦄`: from every `P`-state, `s` terminates without UB in a `Q`-state. -/
def Triple (Pr : Program) (P : Assertion) (s : Stmt) (Q : Assertion) : Prop :=
  ∀ σ, P σ → wp Pr s Q σ

scoped notation "⦃" P "⦄ " s " ⦃" Q "⦄" => Triple [] P s Q

/-! ## What a proof buys you -/

/-- A proved `wp` means the program has **no UB** from `σ`: the interpreter can
never report `stuck`. (Uses `run_stuck_sound`, so determinism matters here too.) -/
theorem wp_not_stuck {Pr : Program} {s : Stmt} {Q : Assertion} {σ : State} (h : wp Pr s Q σ) (n : Nat) :
    run Pr n σ s ≠ .stuck := by
  obtain ⟨σ', hex, _⟩ := h
  intro hrun
  exact run_stuck_sound hrun _ σ' hex

/-! ## Structural rules -/

theorem wp_mono {Pr : Program} {s : Stmt} {Q Q' : Assertion} {σ : State}
    (himp : ∀ σ, Q σ → Q' σ) (h : wp Pr s Q σ) : wp Pr s Q' σ := by
  obtain ⟨σ', hex, hq⟩ := h
  exact ⟨σ', hex, himp _ hq⟩

theorem Triple.conseq {Pr : Program} {P P' Q Q' : Assertion} {s : Stmt}
    (hP : ∀ σ, P' σ → P σ) (h : Triple Pr P s Q) (hQ : ∀ σ, Q σ → Q' σ) :
    Triple Pr P' s Q' :=
  fun σ hp => wp_mono hQ (h σ (hP σ hp))

/-! ## Rules for each statement (all `@[simp]` except `while`) -/

@[simp] theorem wp_skip {Pr : Program} {Q : Assertion} {σ : State} : wp Pr .skip Q σ ↔ Q σ := by
  constructor
  · rintro ⟨σ', h, hq⟩; cases h; exact hq
  · intro hq; exact ⟨σ, .skip, hq⟩

@[simp] theorem wp_assign {Pr : Program} {x : Ident} {e : Expr} {Q : Assertion} {σ : State} :
    wp Pr (.assign x e) Q σ ↔ ∃ v, e.eval σ.st = some v ∧ Q ⟨σ.st.set x v, σ.mem⟩ := by
  obtain ⟨st, m⟩ := σ
  constructor
  · rintro ⟨σ', h, hq⟩; cases h with | assign hv => exact ⟨_, hv, hq⟩
  · rintro ⟨v, hv, hq⟩; exact ⟨_, .assign hv, hq⟩

@[simp] theorem wp_seq {Pr : Program} {s₁ s₂ : Stmt} {Q : Assertion} {σ : State} :
    wp Pr (.seq s₁ s₂) Q σ ↔ wp Pr s₁ (wp Pr s₂ Q) σ := by
  constructor
  · rintro ⟨σ', h, hq⟩
    cases h with
    | seq h₁ h₂ => exact ⟨_, h₁, _, h₂, hq⟩
    | seqAbrupt _ hn => exact absurd rfl hn
  · rintro ⟨σ₁, h₁, σ₂, h₂, hq⟩; exact ⟨σ₂, .seq h₁ h₂, hq⟩

@[simp] theorem wp_ite {Pr : Program} {c : Expr} {s₁ s₂ : Stmt} {Q : Assertion} {σ : State} :
    wp Pr (.ite c s₁ s₂) Q σ ↔
      (c.eval σ.st = some (.bool true) ∧ wp Pr s₁ Q σ) ∨
      (c.eval σ.st = some (.bool false) ∧ wp Pr s₂ Q σ) := by
  constructor
  · rintro ⟨σ', h, hq⟩
    cases h with
    | iteTrue hc h => exact .inl ⟨hc, _, h, hq⟩
    | iteFalse hc h => exact .inr ⟨hc, _, h, hq⟩
  · rintro (⟨hc, σ', h, hq⟩ | ⟨hc, σ', h, hq⟩)
    · exact ⟨σ', .iteTrue hc h, hq⟩
    · exact ⟨σ', .iteFalse hc h, hq⟩

/-- **The loop rule (total correctness).** Supply an invariant `I` and a variant
`μ : Store → Nat`. Three obligations:

* `hcond`: in every invariant state the condition *evaluates* to a boolean (no UB in the guard);
* `hbody`: if the condition is true, the body terminates in a state where `I` still
  holds **and the variant has strictly decreased**;
* `hexit`: if the condition is false, `I` implies the postcondition.

Without `μ` this would be the partial-correctness rule, which is sound only for
"if it terminates". Exercise Sem.2's infinite loop is exactly what `μ` rules out. -/
theorem wp_while {Pr : Program} {c : Expr} {b : Stmt} {Q : Assertion}
    (I : Assertion) (μ : State → Nat)
    (hcond : ∀ σ, I σ → ∃ bv, c.eval σ.st = some (.bool bv))
    (hbody : ∀ σ, I σ → c.eval σ.st = some (.bool true) →
      wp Pr b (fun σ' => I σ' ∧ μ σ' < μ σ) σ)
    (hexit : ∀ σ, I σ → c.eval σ.st = some (.bool false) → Q σ) :
    ∀ σ, I σ → wp Pr (.while c b) Q σ := by
  intro σ
  induction h : μ σ using Nat.strongRecOn generalizing σ with
  | ind k ih =>
    intro hI
    obtain ⟨bv, hc⟩ := hcond σ hI
    cases bv with
    | false => exact ⟨σ, .whileFalse hc, hexit σ hI hc⟩
    | true =>
      obtain ⟨σ₁, hb, hI₁, hlt⟩ := hbody σ hI hc
      obtain ⟨σ₂, hw, hq⟩ := ih (μ σ₁) (h ▸ hlt) σ₁ rfl hI₁
      exact ⟨σ₂, .whileTrue hc hb hw, hq⟩

/-! ## Hoare-style presentations of the same rules

These are what you'd find in a textbook. They're derived from the `wp` lemmas in
one or two lines, which is the payoff of the semantic definition. -/

theorem Triple.skip {Pr : Program} {P : Assertion} : Triple Pr P .skip P := fun _ hp => wp_skip.mpr hp

theorem Triple.seq {Pr : Program} {P Q R : Assertion} {s₁ s₂ : Stmt}
    (h₁ : Triple Pr P s₁ Q) (h₂ : Triple Pr Q s₂ R) : Triple Pr P (.seq s₁ s₂) R :=
  fun σ hp => wp_seq.mpr (wp_mono h₂ (h₁ σ hp))

theorem Triple.assign {Pr : Program} {Q : Assertion} {x : Ident} {e : Expr} :
    Triple Pr (fun σ => ∃ v, e.eval σ.st = some v ∧ Q ⟨σ.st.set x v, σ.mem⟩) (.assign x e) Q :=
  fun _ h => wp_assign.mpr h

theorem Triple.while {Pr : Program} {I : Assertion} {c : Expr} {b : Stmt} (μ : State → Nat)
    (hcond : ∀ σ, I σ → ∃ bv, c.eval σ.st = some (.bool bv))
    (hbody : ∀ n, Triple Pr (fun σ => I σ ∧ c.eval σ.st = some (.bool true) ∧ μ σ = n) b
                         (fun σ => I σ ∧ μ σ < n)) :
    Triple Pr I (.while c b) (fun σ => I σ ∧ c.eval σ.st = some (.bool false)) :=
  wp_while I μ hcond (fun σ hI hc => hbody (μ σ) σ ⟨hI, hc, rfl⟩) (fun _ hI hc => ⟨hI, hc⟩)

/-! ## Functions -/

/-- To prove a function returns `v` satisfying `post`, it suffices to prove the
`wp` of its body from the initial store, with the result evaluation as the
postcondition. -/
theorem Fn.returns_of_wp {Pr : Program} {f : Fn} {args : List Val} {st₀ : Store} {m : Mem}
    {post : Val → Mem → Prop}
    (hinit : f.initStore args = some st₀)
    (hwp : wp Pr f.body (fun σ => ∃ v, f.result.eval σ.st = some v ∧ v.ty = f.ret ∧ post v σ.mem)
      ⟨st₀, m⟩) :
    ∃ v m', f.Returns Pr args m v m' ∧ post v m' := by
  obtain ⟨⟨st₁, m₁⟩, hex, v, hv, hty, hpost⟩ := hwp
  exact ⟨v, m₁, ⟨st₀, .normal, ⟨st₁, m₁⟩, hinit, hex, by simp [Fn.finish, hv, hty], rfl⟩, hpost⟩

end LC
