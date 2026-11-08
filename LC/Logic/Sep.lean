import LC.Logic.Hoare
import LC.Logic.Eval

/-!
# Separation logic for LC (Milestone 3)

## Heaps and assertions

A **heap fragment** is a partial map from addresses `(block, index)` to values. The
memory of a running program gives one (`Mem.heap`), and assertions describe
*fragments* of it. This is B1's construction (Reynolds; Charguéraud), instantiated
with LC's memory.

* `P ∗ Q`: the fragment splits into two disjoint parts satisfying `P` and `Q`.
* `array p xs`: exactly the cells `p[0..len)`, holding `xs`.

## The local weakest precondition

```
swp s Q st h  :=  for every memory m and every frame hf disjoint from h with m = h ⊎ hf,
                  s runs from (st, m) without UB to some (st', m'), where m' = h' ⊎ hf,
                  the frame hf is untouched, and Q st' h' holds.
```

The frame is built into the definition. A proof about `h` therefore holds inside
*any* larger memory, and the **frame rule** (`swp_frame`) is a short lemma. This
"baked-in frame" style is the one used by Charguéraud's CFML/SPLean, Iris's weakest
precondition, Bedrock2, and Certora's Lean Clight `Triple` (LEAN.md §6.1).

The rules below are implications, not iffs, because not every heap fragment is
the whole memory of some program. Use them backwards, with `apply`, from the
postcondition to the precondition.
-/

namespace LC

abbrev Addr := Nat × Nat
abbrev Heap := Addr → Option Val

/-- The heap view of a concrete memory. -/
def Mem.heap (m : Mem) : Heap := fun a => m.read a.1 a.2

namespace Heap

def empty : Heap := fun _ => none
def Disjoint (h₁ h₂ : Heap) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none
def union (h₁ h₂ : Heap) : Heap := fun a => (h₁ a).or (h₂ a)
def update (h : Heap) (a : Addr) (v : Val) : Heap := fun a' => if a' = a then some v else h a'

theorem Disjoint.symm {h₁ h₂ : Heap} (d : h₁.Disjoint h₂) : h₂.Disjoint h₁ :=
  fun a => (d a).symm

theorem union_comm {h₁ h₂ : Heap} (d : h₁.Disjoint h₂) : h₁.union h₂ = h₂.union h₁ := by
  funext a; unfold union; rcases d a with h | h <;> simp [h]

theorem union_assoc (h₁ h₂ h₃ : Heap) : (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  funext a; unfold union; cases h₁ a <;> simp

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro d
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> rcases d a with h | h <;> simp_all [union]
  · rintro ⟨d₁, d₂⟩ a
    rcases d₁ a with h | h <;> rcases d₂ a with h' | h' <;> simp [union, h, h']

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro d; have := disjoint_union_left.mp d.symm; exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨d₁, d₂⟩; exact (disjoint_union_left.mpr ⟨d₁.symm, d₂.symm⟩).symm

theorem union_get_left {h₁ h₂ : Heap} {a : Addr} {v : Val} (h : h₁ a = some v) :
    (h₁.union h₂) a = some v := by simp [union, h]

theorem union_get_right {h₁ h₂ : Heap} {a : Addr} {v : Val}
    (d : h₁.Disjoint h₂) (h : h₂ a = some v) : (h₁.union h₂) a = some v := by
  rcases d a with h' | h' <;> simp_all [union]

/-- Writing into the left part of a disjoint union. -/
theorem update_union_left {h₁ h₂ : Heap} {a : Addr} {v : Val} (ha : h₂ a = none) :
    (h₁.union h₂).update a v = (h₁.update a v).union h₂ := by
  funext a'; unfold update union; by_cases e : a' = a <;> simp [e, ha]

theorem disjoint_update_left {h₁ h₂ : Heap} {a : Addr} {v : Val}
    (d : h₁.Disjoint h₂) (ha : h₂ a = none) : (h₁.update a v).Disjoint h₂ := by
  intro a'; unfold update; by_cases e : a' = a
  · subst e; exact .inr ha
  · simp [e]; exact d a'

end Heap

/-! ## Assertions -/

abbrev HProp := Heap → Prop

def HProp.star (P Q : HProp) : HProp :=
  fun h => ∃ h₁ h₂, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P h₁ ∧ Q h₂

scoped infixr:35 " ∗ " => HProp.star

/-- `array p xs` owns exactly the cells `p[0] … p[len-1]`, which hold `xs`. -/
def array (p : Ptr) (xs : List Val) : HProp := fun h =>
  ∀ a, h a = if a.1 = p.blk ∧ p.off ≤ a.2 then xs[a.2 - p.off]? else none

theorem HProp.star_comm {P Q : HProp} {h : Heap} : (P ∗ Q) h → (Q ∗ P) h := by
  rintro ⟨h₁, h₂, d, rfl, hp, hq⟩
  exact ⟨h₂, h₁, d.symm, Heap.union_comm d, hq, hp⟩

theorem array_get {p : Ptr} {xs : List Val} {h : Heap} (ha : array p xs h)
    {k : Nat} (hk : k < xs.length) : h (p.blk, p.off + k) = some xs[k] := by
  rw [ha]; simp [List.getElem?_eq_getElem hk]

theorem array_update {p : Ptr} {xs : List Val} {h : Heap} (ha : array p xs h)
    {k : Nat} (hk : k < xs.length) (v : Val) :
    array p (xs.set k v) (h.update (p.blk, p.off + k) v) := by
  intro ⟨b, j⟩
  simp only [Heap.update, Prod.mk.injEq]
  by_cases e : b = p.blk ∧ j = p.off + k
  · obtain ⟨rfl, rfl⟩ := e; simp [hk]
  · simp only [e, ite_false]; rw [ha]
    by_cases e2 : b = p.blk ∧ p.off ≤ j
    · simp only [e2, and_self, ite_true]
      rw [List.getElem?_set]; split
      · omega
      · rfl
    · simp [e2]

/-- Reading a cell owned by the left part of `P ∗ Q`. -/
theorem star_get_left {P Q : HProp} {h : Heap} {a : Addr} {v : Val}
    (hpq : (P ∗ Q) h) (hp : ∀ h₁, P h₁ → h₁ a = some v) : h a = some v := by
  obtain ⟨h₁, h₂, _, rfl, hP, _⟩ := hpq
  exact Heap.union_get_left (hp h₁ hP)

theorem star_get_right {P Q : HProp} {h : Heap} {a : Addr} {v : Val}
    (hpq : (P ∗ Q) h) (hq : ∀ h₂, Q h₂ → h₂ a = some v) : h a = some v := by
  obtain ⟨h₁, h₂, d, rfl, _, hQ⟩ := hpq
  exact Heap.union_get_right d (hq h₂ hQ)

/-- Writing a cell owned by the left part of `P ∗ Q` leaves `Q` untouched. -/
theorem star_update_left {P P' Q : HProp} {h : Heap} {a : Addr} {v : Val}
    (hpq : (P ∗ Q) h) (hp : ∀ h₁, P h₁ → h₁ a ≠ none ∧ P' (h₁.update a v)) :
    (P' ∗ Q) (h.update a v) := by
  obtain ⟨h₁, h₂, d, rfl, hP, hQ⟩ := hpq
  obtain ⟨hne, hP'⟩ := hp h₁ hP
  have h₂a : h₂ a = none := by rcases d a with e | e <;> simp_all
  exact ⟨_, h₂, Heap.disjoint_update_left d h₂a, Heap.update_union_left h₂a, hP', hQ⟩

/-! ## Memory lemmas: how `Mem.read`/`Mem.write` look through `Mem.heap` -/

theorem Mem.cells_setCells (m : Mem) (b b' : Nat) (cs : List Val) :
    (m.setCells b cs).cells b' = if b = b' ∧ (m.cells b).isSome then some cs else m.cells b' := by
  induction m with
  | nil => simp [Mem.setCells, Mem.cells]
  | cons e m ih =>
    obtain ⟨c, ds⟩ := e
    by_cases h1 : c = b
    · subst h1
      by_cases h2 : c = b' <;> simp [Mem.setCells, Mem.cells, h2]
    · by_cases h2 : c = b'
      · subst h2; simp [Mem.setCells, Mem.cells, h1, Ne.symm h1]
      · simp [Mem.setCells, Mem.cells, h1, h2, ih]

theorem Mem.write_heap {m : Mem} {b k : Nat} {v₀ : Val} (hr : m.read b k = some v₀) (v : Val) :
    ∃ m', m.write b k v = some m' ∧ m'.heap = m.heap.update (b, k) v := by
  unfold Mem.read at hr
  cases hc : m.cells b with
  | none => simp [hc] at hr
  | some cs =>
    simp only [hc, Option.bind_some] at hr
    obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp hr
    refine ⟨m.setCells b (cs.set k v), by simp [Mem.write, hc, hk], ?_⟩
    funext ⟨b', k'⟩
    simp only [Mem.heap, Mem.read, Heap.update, Prod.mk.injEq, Mem.cells_setCells, hc,
      Option.isSome_some, and_true]
    by_cases e1 : b = b'
    · subst e1; simp only [ite_true, Option.bind_some, List.getElem?_set, hc, true_and]
      by_cases e2 : k' = k
      · subst e2; simp [hk]
      · simp [e2, Ne.symm e2]
    · simp [e1, Ne.symm e1]

/-! ## The local weakest precondition -/

/-- Assertions over the store and the owned heap fragment. -/
abbrev SProp := Store → HProp

def swp (s : Stmt) (Q : SProp) (st : Store) (h : Heap) : Prop :=
  ∀ (m : Mem) (hf : Heap), h.Disjoint hf → m.heap = h.union hf →
    ∃ st' m' h', Exec ⟨st, m⟩ s ⟨st', m'⟩ ∧ h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ Q st' h'

/-- Separation-logic triple: from any `P`-state, in any surrounding memory, `s`
terminates without UB in a `Q`-state, leaving the rest of memory alone. -/
def STriple (P : SProp) (s : Stmt) (Q : SProp) : Prop :=
  ∀ st h, P st h → swp s Q st h

theorem swp_mono {s : Stmt} {Q Q' : SProp} {st : Store} {h : Heap}
    (himp : ∀ st h, Q st h → Q' st h) (hw : swp s Q st h) : swp s Q' st h := by
  intro m hf d hm
  obtain ⟨st', m', h', hex, d', hm', hq⟩ := hw m hf d hm
  exact ⟨st', m', h', hex, d', hm', himp _ _ hq⟩

/-- **The frame rule.** Whatever `s` doesn't own, it leaves alone. -/
theorem swp_frame {s : Stmt} {Q : SProp} {R : HProp} {st : Store} {h₁ h₂ : Heap}
    (hw : swp s Q st h₁) (hr : R h₂) (d : h₁.Disjoint h₂) :
    swp s (fun st' => Q st' ∗ R) st (h₁.union h₂) := by
  intro m hf dhf hm
  obtain ⟨d₁, d₂⟩ := Heap.disjoint_union_left.mp dhf
  obtain ⟨st', m', h₁', hex, d', hm', hq⟩ :=
    hw m (h₂.union hf) (Heap.disjoint_union_right.mpr ⟨d, d₁⟩) (by rw [hm, Heap.union_assoc])
  obtain ⟨d'₂, d'f⟩ := Heap.disjoint_union_right.mp d'
  refine ⟨st', m', h₁'.union h₂, hex, Heap.disjoint_union_left.mpr ⟨d'f, d₂⟩,
    by rw [hm', Heap.union_assoc], h₁', h₂, d'₂, rfl, hq, hr⟩

theorem swp_skip {Q : SProp} {st : Store} {h : Heap} (hq : Q st h) : swp .skip Q st h :=
  fun m _ d hm => ⟨st, m, h, .skip, d, hm, hq⟩

theorem swp_assign {x : Ident} {e : Expr} {Q : SProp} {st : Store} {h : Heap} {v : Val}
    (hv : e.eval st = some v) (hq : Q (st.set x v) h) : swp (.assign x e) Q st h :=
  fun m _ d hm => ⟨st.set x v, m, h, .assign hv, d, hm, hq⟩

theorem swp_seq {s₁ s₂ : Stmt} {Q : SProp} {st : Store} {h : Heap}
    (hw : swp s₁ (swp s₂ Q) st h) : swp (.seq s₁ s₂) Q st h := by
  intro m hf d hm
  obtain ⟨st₁, m₁, h₁, hex₁, d₁, hm₁, hw₂⟩ := hw m hf d hm
  obtain ⟨st₂, m₂, h₂, hex₂, d₂, hm₂, hq⟩ := hw₂ m₁ hf d₁ hm₁
  exact ⟨st₂, m₂, h₂, .seq hex₁ hex₂, d₂, hm₂, hq⟩

theorem swp_ite {c : Expr} {s₁ s₂ : Stmt} {Q : SProp} {st : Store} {h : Heap}
    (hw : (c.eval st = some (.bool true) ∧ swp s₁ Q st h) ∨
          (c.eval st = some (.bool false) ∧ swp s₂ Q st h)) :
    swp (.ite c s₁ s₂) Q st h := by
  intro m hf d hm
  rcases hw with ⟨hc, hw⟩ | ⟨hc, hw⟩
  · obtain ⟨st', m', h', hex, r⟩ := hw m hf d hm; exact ⟨st', m', h', .iteTrue hc hex, r⟩
  · obtain ⟨st', m', h', hex, r⟩ := hw m hf d hm; exact ⟨st', m', h', .iteFalse hc hex, r⟩

/-- `x = p[i];` reads a cell that the precondition **owns**, so it must be in bounds. -/
theorem swp_load {x : Ident} {p i : Expr} {Q : SProp} {st : Store} {h : Heap}
    {t : IntTy} {b k : Nat} {v : Val}
    (ha : Expr.evalAddr st p i = some (t, b, k)) (hcell : h (b, k) = some v)
    (hty : v.ty = .int t) (hq : Q (st.set x v) h) : swp (.load x p i) Q st h := by
  intro m hf d hm
  have hr : m.read b k = some v := by
    show m.heap (b, k) = some v; rw [hm]; exact Heap.union_get_left hcell
  exact ⟨st.set x v, m, h, .load ha hr hty, d, hm, hq⟩

/-- `p[i] = e;` writes a cell that the precondition owns. The postcondition sees
the updated fragment, and the frame is untouched. -/
theorem swp_store {p i e : Expr} {Q : SProp} {st : Store} {h : Heap}
    {t : IntTy} {b k : Nat} {v v₀ : Val}
    (ha : Expr.evalAddr st p i = some (t, b, k)) (hv : e.eval st = some v)
    (hty : v.ty = .int t) (hcell : h (b, k) = some v₀)
    (hq : Q st (h.update (b, k) v)) : swp (.store p i e) Q st h := by
  intro m hf d hm
  have hr : m.read b k = some v₀ := by
    show m.heap (b, k) = some v₀; rw [hm]; exact Heap.union_get_left hcell
  obtain ⟨m', hw, hm'⟩ := Mem.write_heap hr v
  have hfa : hf (b, k) = none := by rcases d (b, k) with e | e <;> simp_all
  exact ⟨st, m', h.update (b, k) v, .store ha hv hty hw, Heap.disjoint_update_left d hfa,
    by rw [hm', hm, Heap.update_union_left hfa], hq⟩

/-- **The loop rule**, exactly like `wp_while` but over (store, owned fragment). -/
theorem swp_while {c : Expr} {b : Stmt} {Q : SProp}
    (I : SProp) (μ : Store → Heap → Nat)
    (hcond : ∀ st h, I st h → ∃ bv, c.eval st = some (.bool bv))
    (hbody : ∀ st h, I st h → c.eval st = some (.bool true) →
      swp b (fun st' h' => I st' h' ∧ μ st' h' < μ st h) st h)
    (hexit : ∀ st h, I st h → c.eval st = some (.bool false) → Q st h) :
    ∀ st h, I st h → swp (.while c b) Q st h := by
  intro st h
  induction hk : μ st h using Nat.strongRecOn generalizing st h with
  | ind k ih =>
    intro hI m hf d hm
    obtain ⟨bv, hc⟩ := hcond st h hI
    cases bv with
    | false => exact ⟨st, m, h, .whileFalse hc, d, hm, hexit st h hI hc⟩
    | true =>
      obtain ⟨st₁, m₁, h₁, hex₁, d₁, hm₁, hI₁, hlt⟩ := hbody st h hI hc m hf d hm
      obtain ⟨st₂, m₂, h₂, hex₂, d₂, hm₂, hq⟩ :=
        ih (μ st₁ h₁) (hk ▸ hlt) st₁ h₁ rfl hI₁ m₁ hf d₁ hm₁
      exact ⟨st₂, m₂, h₂, .whileTrue hc hex₁ hex₂, d₂, hm₂, hq⟩

/-! ## Forms that `simp` can drive

The rules above take the computed value as an argument. These variants put it under
an `∃`, so after `apply`, `simp` can compute the expression and fill it in, just
as in M2's `wp_assign`. -/

theorem swp_assign' {x : Ident} {e : Expr} {Q : SProp} {st : Store} {h : Heap}
    (hw : ∃ v, e.eval st = some v ∧ Q (st.set x v) h) : swp (.assign x e) Q st h :=
  let ⟨_, hv, hq⟩ := hw; swp_assign hv hq

theorem swp_load' {x : Ident} {p i : Expr} {Q : SProp} {st : Store} {h : Heap}
    (hw : ∃ t b k, Expr.evalAddr st p i = some (t, b, k) ∧
      ∃ v, h (b, k) = some v ∧ v.ty = .int t ∧ Q (st.set x v) h) :
    swp (.load x p i) Q st h :=
  let ⟨_, _, _, ha, _, hc, hty, hq⟩ := hw; swp_load ha hc hty hq

theorem swp_store' {p i e : Expr} {Q : SProp} {st : Store} {h : Heap}
    (hw : ∃ t b k, Expr.evalAddr st p i = some (t, b, k) ∧
      ∃ v, e.eval st = some v ∧ v.ty = .int t ∧ (∃ v₀, h (b, k) = some v₀) ∧
        Q st (h.update (b, k) v)) :
    swp (.store p i e) Q st h :=
  let ⟨_, _, _, ha, _, hv, hty, ⟨_, hc⟩, hq⟩ := hw; swp_store ha hv hty hc hq

/-! ## Functions -/

/-- From a local `swp` of the body to a fact about calling the function in *any*
memory containing the fragment `h`. -/
theorem Fn.returns_of_swp {f : Fn} {args : List Val} {st₀ : Store} {h hf : Heap} {m : Mem}
    {post : Val → HProp}
    (hinit : f.initStore args = some st₀)
    (hw : swp f.body (fun st h' => ∃ v, f.result.eval st = some v ∧ v.ty = f.ret ∧ post v h') st₀ h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', f.Returns args m v m' ∧ h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ post v h' := by
  obtain ⟨st₁, m', h', hex, d', hm', v, hv, hty, hpost⟩ := hw m hf d hm
  exact ⟨v, m', h', ⟨st₀, st₁, hinit, hex, hv, hty⟩, d', hm', hpost⟩

end LC
