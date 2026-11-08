/-
B1 — Separation logic from scratch, in 40 lines.   Run:  lean exercises/core/B1_Sep.lean

A heap is a partial map; an assertion is a predicate on heaps. `P ∗ Q` holds of a
heap that splits into two DISJOINT parts, one satisfying P, the other Q.
This is the shallow-assertion style (Reynolds; Charguéraud; Bedrock2) we'll use in M3.
-/

abbrev Heap := Nat → Option Int
def Heap.disjoint (h1 h2 : Heap) : Prop := ∀ a, h1 a = none ∨ h2 a = none
def Heap.union (h1 h2 : Heap) : Heap := fun a => (h1 a).or (h2 a)
abbrev HProp := Heap → Prop
def emp : HProp := fun h => ∀ a, h a = none
def pointsTo (p : Nat) (v : Int) : HProp := fun h => h p = some v ∧ ∀ a, a ≠ p → h a = none
def star (P Q : HProp) : HProp :=
  fun h => ∃ h1 h2, h1.disjoint h2 ∧ h = h1.union h2 ∧ P h1 ∧ Q h2
infixr:35 " ∗ " => star

-- (1) Union is commutative *on disjoint heaps*. Why would it fail without disjointness?
--     Hint: `funext a; unfold Heap.union; rcases d a with h | h <;> simp [h]`
theorem Heap.union_comm (h1 h2 : Heap) (d : h1.disjoint h2) : h1.union h2 = h2.union h1 := by
  sorry

-- (2) ∗ is commutative.  Hint: `rintro ⟨h1, h2, d, rfl, hp, hq⟩` then build the witness.
theorem star_comm (P Q : HProp) (h : Heap) : (P ∗ Q) h → (Q ∗ P) h := by
  sorry

-- (3) THE point of separation logic: two separate points-to facts ⇒ no aliasing.
--     In Low*-style Hoare logic you would have to carry `p ≠ q` around by hand.
theorem pointsTo_distinct (p q : Nat) (v w : Int) (h : Heap) :
    (pointsTo p v ∗ pointsTo q w) h → p ≠ q := by
  sorry

-- (4) Think: is `pointsTo p v ∗ pointsTo p v` satisfiable? What does that tell you
--     about how `∗` differs from `∧`?
