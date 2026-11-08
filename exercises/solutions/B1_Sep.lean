-- Solution to exercises/core/B1_Sep.lean. (4): unsatisfiable — both halves would need address p, but they are disjoint. ∗ is resource-counting; ∧ is not.
abbrev Heap := Nat → Option Int
def Heap.disjoint (h1 h2 : Heap) : Prop := ∀ a, h1 a = none ∨ h2 a = none
def Heap.union (h1 h2 : Heap) : Heap := fun a => (h1 a).or (h2 a)
abbrev HProp := Heap → Prop
def emp : HProp := fun h => ∀ a, h a = none
def pointsTo (p : Nat) (v : Int) : HProp := fun h => h p = some v ∧ ∀ a, a ≠ p → h a = none
def star (P Q : HProp) : HProp :=
  fun h => ∃ h1 h2, h1.disjoint h2 ∧ h = h1.union h2 ∧ P h1 ∧ Q h2
infixr:35 " ∗ " => star

theorem Heap.union_comm (h1 h2 : Heap) (d : h1.disjoint h2) : h1.union h2 = h2.union h1 := by
  funext a; unfold Heap.union; rcases d a with h | h <;> simp [h]

theorem star_comm (P Q : HProp) (h : Heap) : (P ∗ Q) h → (Q ∗ P) h := by
  rintro ⟨h1, h2, d, rfl, hp, hq⟩
  exact ⟨h2, h1, fun a => (d a).symm, Heap.union_comm _ _ d, hq, hp⟩

-- the key fact separation buys you: two separate points-to facts mean distinct addresses
theorem pointsTo_distinct (p q : Nat) (v w : Int) (h : Heap) :
    (pointsTo p v ∗ pointsTo q w) h → p ≠ q := by
  rintro ⟨h1, h2, d, -, ⟨hp, -⟩, ⟨hq, -⟩⟩ rfl
  rcases d p with e | e <;> simp_all
