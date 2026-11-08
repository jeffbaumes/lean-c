import LC.Typing
import LC.Semantics
import LC.Logic.Eval

/-!
# Type preservation

If an expression has type `τ` and the store respects the typing environment, then
any value it evaluates to has type `τ`. Statements preserve the store invariant.

Together these say that **type errors can't appear at runtime**: every `none` from a
well-typed program comes from a value-dependent check (overflow, division by zero,
shift amount, uninitialised read). Those are exactly the obligations the program
logic leaves you.

(The other half, *progress*, says a well-typed expression over an initialised store
gets stuck only for those value reasons. It needs a precise list of UB conditions and
is better stated alongside a VC generator.)
-/

namespace LC

/-- Every initialised variable holds a value of its declared type. -/
def StoreTyped (Γ : TyEnv) (σ : Store) : Prop :=
  ∀ x v, σ.get x = some v → Γ x = some v.ty

theorem IntTy.ofInt?_ty {t : IntTy} {z : Int} {v : Val} (h : t.ofInt? z = some v) :
    v.ty = .int t := by
  unfold IntTy.ofInt? at h; split at h <;> simp_all; subst h; rfl

theorem intBinOp_ty {op : BinOp} {t : IntTy} {a b : BitVec t.bits} {v : Val}
    (h : intBinOp op t a b = some v) :
    v.ty = (match op with
      | .eq | .ne | .lt | .le | .land | .lor => Ty.bool
      | _ => .int t) := by
  cases op <;> simp only [intBinOp] at h <;> (repeat' split at h) <;>
    first
    | (cases h; rfl)
    | exact IntTy.ofInt?_ty h
    | (obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.mp h; exact IntTy.ofInt?_ty h)
    | simp at h

theorem evalUnOp_ty {op : UnOp} {x v : Val} {τ : Ty}
    (hty : (match op, x.ty with
      | .neg, .int t => some (.int t)
      | .bnot, .int t => some (.int t)
      | .lnot, .bool => some .bool
      | _, _ => none) = some τ)
    (h : evalUnOp op x = some v) : v.ty = τ := by
  cases op <;> cases x <;> simp_all [evalUnOp, Val.ty] <;> (repeat' split at h) <;>
    first
    | (cases h; subst hty; rfl)
    | (subst hty; exact IntTy.ofInt?_ty h)
    | simp_all

theorem evalCast_ty {t : IntTy} {x v : Val} (h : evalCast t x = some v) : v.ty = .int t := by
  cases x <;> simp [evalCast, Val.toInt?] at h
  split at h
  · exact IntTy.ofInt?_ty h
  · cases h; rfl

theorem Expr.typeOf_sound {Γ : TyEnv} {σ : Store} (hσ : StoreTyped Γ σ) :
    ∀ (e : Expr) {τ : Ty} {v : Val}, e.typeOf Γ = some τ → e.eval σ = some v → v.ty = τ := by
  intro e
  induction e with
  | lit val =>
    intro τ v ht he; simp [Expr.eval] at he; subst he
    cases val <;> simp_all [Expr.typeOf, Val.ty]
  | var x => intro τ v ht he; simp [Expr.typeOf, Expr.eval] at ht he; have := hσ x v he; simp_all
  | unop op e ih =>
    intro τ v ht he
    simp only [Expr.typeOf, Expr.eval] at ht he
    obtain ⟨te, hte, ht⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    have := ih hte hx
    subst this
    exact evalUnOp_ty ht he
  | cast t e ih =>
    intro τ v ht he
    simp only [Expr.typeOf, Expr.eval] at ht he
    obtain ⟨te, hte, ht⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.mp he
    cases te <;> simp at ht
    subst ht; exact evalCast_ty he
  | binop op a b iha ihb =>
    intro τ v ht he
    simp only [Expr.typeOf, bind, Option.bind_eq_some_iff] at ht
    obtain ⟨ta, hta, tb, htb, ht⟩ := ht
    split at ht
    · simp at ht
    rename_i hab; simp only [Decidable.not_not] at hab; subst hab
    cases op
    case land | lor =>
      cases ta <;> simp at ht; subst ht
      simp only [Expr.eval] at he
      repeat' split at he
      all_goals first | (cases he; rfl) | simp at he
    all_goals
      simp only [Expr.eval, bind, Option.bind_eq_some_iff] at he
      obtain ⟨va, hva, vb, hvb, he⟩ := he
      have h1 := iha hta hva
      have h2 := ihb htb hvb
      cases va <;> cases vb <;> simp only [Val.ty] at h1 h2 <;> subst h1 <;>
        (try simp only [Ty.int.injEq, Ty.ptr.injEq, reduceCtorEq] at h2)
    -- int ⊕ int: the result type is what `intBinOp_ty` computes; bool ⊕ bool: only ==/!=
    all_goals first
      | (subst h2; rw [evalBinOp_int] at he; have hv := intBinOp_ty he
         simp only at hv ht; (repeat' split at ht) <;> simp_all)
      | (simp [evalBinOp] at he; (repeat' split at he) <;> simp_all <;> (cases he; simp_all [Val.ty]))
      | simp [evalBinOp] at he
      | simp at ht

theorem StoreTyped.set {Γ : TyEnv} {σ : Store} {x : Ident} {v : Val}
    (hσ : StoreTyped Γ σ) (hx : Γ x = some v.ty) : StoreTyped Γ (σ.set x v) := by
  intro y w hy
  by_cases h : y = x
  · subst h; simp at hy; subst hy; exact hx
  · rw [Store.get_set_other _ _ _ _ h] at hy; exact hσ y w hy

/-- Executing a well-typed statement keeps every variable at its declared type. -/
theorem Exec.preserves_typed {Γ : TyEnv} {σ σ' : State} {s : Stmt}
    (h : Exec σ s σ') (hwt : s.typeCheck Γ = true) (hσ : StoreTyped Γ σ.st) :
    StoreTyped Γ σ'.st := by
  induction h with
  | skip => exact hσ
  | @assign st m x e v hv =>
    simp only [Stmt.typeCheck, Bool.and_eq_true, Option.isSome_iff_exists, beq_iff_eq] at hwt
    obtain ⟨⟨τ, hτ⟩, heq⟩ := hwt
    have := Expr.typeOf_sound hσ e (heq ▸ hτ) hv
    exact StoreTyped.set hσ (by rw [hτ, this])
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.typeCheck, Bool.and_eq_true] at hwt
    exact ih₂ hwt.2 (ih₁ hwt.1 hσ)
  | iteTrue _ _ ih =>
    simp only [Stmt.typeCheck, Bool.and_eq_true] at hwt; exact ih hwt.1.2 hσ
  | iteFalse _ _ ih =>
    simp only [Stmt.typeCheck, Bool.and_eq_true] at hwt; exact ih hwt.2 hσ
  | whileTrue _ _ _ ihb ihw =>
    have hw := hwt
    simp only [Stmt.typeCheck, Bool.and_eq_true] at hwt
    exact ihw hw (ihb hwt.2 hσ)
  | whileFalse _ => exact hσ
  | @load st m x p i t b k v ha _ hty =>
    -- the dynamic check `v.ty = .int t` plus the static `Γ x = ptr's element type`
    simp only [Stmt.typeCheck] at hwt
    split at hwt
    · next t' hp =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hwt
      have ht' : t' = t := by
        simp only [Expr.evalAddr] at ha
        split at ha
        · next b' off k' hpv hiv =>
          cases ha
          have := Expr.typeOf_sound hσ p hp hpv
          simp [Val.ty] at this; exact this.symm
        · simp at ha
      subst ht'
      exact StoreTyped.set hσ (by rw [hwt.2, hty])
    · simp at hwt
  | store => exact hσ

end LC
