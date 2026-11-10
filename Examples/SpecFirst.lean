import LC

/-!
# Spec first: `is_sorted`, from a reference function to a refinement proof

```c
bool is_sorted(uint32_t *a, uint32_t n);   // a[0..n) is non-decreasing
```

This file is the spec-first workflow, in order (see docs/spec-first.md):

1. **Reference.** The spec is a plain Lean function, written for obviousness, not speed.
2. **Test the reference.** `#guard`s and random properties against an independent oracle. The
   spec is the one thing a proof can't check, and the thing a human reviews.
3. **Code.** The LC function, type-checked and printable as C.
4. **Test the code against the reference**, on random inputs, in the interpreter.
5. **Prove** that the code refines the reference: it returns exactly what the reference
   computes. With `lc_auto`, that's the invariant plus three short lemmas.

Steps 2 and 4 are cheap and catch most mistakes before any proof effort is spent.
-/

open LC LC.Check

namespace Examples.SpecFirst

/-! ## 1. The reference

"Sorted" means every element is `≤` every later one (as unsigned numbers). The code will only
compare *neighbours*; the reference deliberately doesn't, so that the proof shows the two agree. -/

def SortedRef (xs : List (BitVec 32)) : Prop := xs.Pairwise (fun a b => a.toNat ≤ b.toNat)

instance (xs : List (BitVec 32)) : Decidable (SortedRef xs) := by unfold SortedRef; infer_instance

/-- The reference, as the value `is_sorted` must return. -/
def isSortedRef (xs : List (BitVec 32)) : Bool := decide (SortedRef xs)

/-! ## 2. Test the reference

Unit examples first, including the edge cases a reviewer would ask about. -/

#guard isSortedRef []
#guard isSortedRef [5]
#guard isSortedRef [1, 2, 2, 3]                 -- equal neighbours are allowed
#guard !isSortedRef [2, 1]
#guard !isSortedRef [1, 3, 2, 4]
#guard isSortedRef [0, 0x80000000, 0xffffffff]  -- unsigned order, not signed

/-- Lists that are often sorted (or nearly), with small values so that ties happen. -/
def genList : Gen (List (BitVec 32)) :=
  Gen.frequency [(1, Gen.list 8 (Gen.bvSmall 32)), (1, Gen.sortedList 8 (Gen.bvSmall 32))]

-- An independent oracle: sorting a sorted list changes nothing, and nothing else is fixed by it.
#guard forAll genList fun xs => isSortedRef xs == (xs.mergeSort (·.toNat ≤ ·.toNat) == xs)
-- Every sorted list's prefixes and suffixes are sorted.
#guard forAll genList fun xs => !isSortedRef xs || (List.range (xs.length + 1)).all fun k =>
  isSortedRef (xs.take k) && isSortedRef (xs.drop k)
-- The generator really produces both outcomes (a test that only ever sees `true` proves little).
#guard (samples genList).any isSortedRef && (samples genList).any (! isSortedRef ·)

/-! ## 3. The code

```c
bool is_sorted(uint32_t *a, uint32_t n) {
  uint32_t i = 1u;
  while (i < n) {
    if (a[i] < a[i - 1u]) return false;
    i = i + 1u;
  }
  return true;
}
```
-/

def isSorted : Fn where
  name   := "is_sorted"
  params := [("a", .ptr .u32), ("n", .int .u32)]
  locals := [("i", .int .u32), ("x", .int .u32), ("y", .int .u32)]
  body   := .block [
    "i" ::= .u32 1,
    .while (v "i" <. v "n") (.block [
      .load "x" (v "a") (v "i" - .u32 1),
      .load "y" (v "a") (v "i"),
      .ite (v "y" <. v "x") (.ret .ff) .skip,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .bool
  result := .tt

#guard isSorted.typeCheck
#guard (cTranslationUnit [isSorted]).isOk

/-! ## 4. Test the code against the reference

`runIsSorted xs` lays `xs` out in block 0 and runs `is_sorted` in the interpreter. -/

def runIsSorted (xs : List (BitVec 32)) : Option Bool :=
  let cells := u32s xs
  match isSorted.callMem [.ptr .u32 ⟨0, 0⟩, .u32 xs.length]
      [(0, if cells.isEmpty then [.u32 0] else cells)] with
  | .ok (.bool b, _) => some b
  | _ => none

#guard forAll genList fun xs => runIsSorted xs == some (isSortedRef xs)
-- If this fails, see the input with:
-- #eval counterexample? genList fun xs => runIsSorted xs == some (isSortedRef xs)

/-! ## 5. The proof: `is_sorted` refines `isSortedRef`

The invariant says the neighbours before `i` are in order. Three lemmas connect that to the
reference; `lc_auto` does everything else. -/

/-- Neighbours `j, j+1` with `j + 1 < i` are in order. -/
def AdjSorted (xs : List (BitVec 32)) (i : Nat) : Prop :=
  ∀ j a b, j + 1 < i → xs[j]? = some a → xs[j + 1]? = some b → a.toNat ≤ b.toNat

def sortedInv (p : Ptr) (xs : List (BitVec 32)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, 1 ≤ i ∧ (i ≤ xs.length ∨ i = 1) ∧ st.get "a" = some (.ptr .u32 p) ∧
    st.get "n" = some (nu32 xs.length) ∧ st.get "i" = some (nu32 i) ∧ AdjSorted xs i ∧ h = h₀

/-- One more neighbour pair checked. -/
theorem adj_succ {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) (hadj : AdjSorted xs i)
    (hle : xs[i - 1].toNat ≤ xs[i].toNat) : AdjSorted xs (i + 1) := by
  intro j a b hj hja hjb
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · exact hadj j a b hj hja hjb
  · obtain rfl : j = i - 1 := by omega
    rw [List.getElem?_eq_getElem (by omega)] at hja
    rw [show i - 1 + 1 = i by omega, List.getElem?_eq_getElem hi] at hjb
    cases hja; cases hjb; exact hle

/-- All neighbours in order means sorted (the reference's sense). -/
theorem sorted_of_adj {xs : List (BitVec 32)} {k : Nat} (hadj : AdjSorted xs k)
    (hge : xs.length ≤ k) : isSortedRef xs = true := by
  have step : ∀ d i (_hid : i + d < xs.length) (hi : i < xs.length),
      xs[i].toNat ≤ xs[i + d].toNat := by
    intro d
    induction d with
    | zero => intros; exact Nat.le_refl _
    | succ d ih =>
      intro i hid hi
      have := ih i (by omega) hi
      have := hadj (i + d) _ _ (by omega) (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem (by omega))
      simp only [← Nat.add_assoc]; omega
  simp only [isSortedRef, decide_eq_true_eq, SortedRef, List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := step (j - i) i (by omega) hi
  simpa [show i + (j - i) = j by omega] using this

/-- Before the loop, there are no pairs to check. -/
theorem adj_one (xs : List (BitVec 32)) : AdjSorted xs 1 := fun j _ _ hj => by omega

/-- A pair of neighbours out of order means not sorted. -/
theorem not_sorted_of_desc {xs : List (BitVec 32)} {i : Nat} (hi : i < xs.length) (h1 : 1 ≤ i)
    (hlt : xs[i].toNat < xs[i - 1].toNat) : isSortedRef xs = false := by
  simp only [isSortedRef, decide_eq_false_iff_not, SortedRef, List.pairwise_iff_getElem]
  intro h
  have := h (i - 1) i (by omega) hi (by omega)
  omega

/-- **`is_sorted` returns exactly `isSortedRef xs`**, for any array of length < 2³², inside any
memory, and leaves memory unchanged. -/
theorem isSorted_refines (P : Program) (p : Ptr) (xs : List (BitVec 32))
    (hlen : xs.length < 2 ^ 32) (h hf : Heap) (m : Mem) (ha : array p (u32s xs) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m', isSorted.Returns P [.ptr .u32 p, .u32 xs.length] m (.bool (isSortedRef xs)) m' ∧
      m'.heap = m.heap := by
  have hinit : isSorted.initStore [.ptr .u32 p, .u32 xs.length] =
      some [("a", .ptr .u32 p), ("n", nu32 xs.length)] := by
    simp [Fn.initStore, isSorted, Store.empty]; constructor <;> rfl
  suffices hbody : swpo P isSorted.body (fun o st h' => ∃ v, isSorted.finish o st = some v ∧
      (v = .bool (isSortedRef xs) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swpo
      (post := fun v h' => v = .bool (isSortedRef xs) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (sortedInv p xs h) (counterVariant xs.length) [sortedInv, counterVariant]
  · exact not_sorted_of_desc ‹_› ‹_› ‹_›
  · exact adj_succ ‹_› ‹_› ‹_›
  · exact sorted_of_adj ‹_› ‹_›
  · exact adj_one xs

end Examples.SpecFirst

#print axioms Examples.SpecFirst.isSorted_refines
