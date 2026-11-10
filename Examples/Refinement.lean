import Examples.SpecFirst
import Examples.Search
import Examples.ParseU32

/-!
# The earlier specs, restated as reference functions

`parse_u32` and `lower_bound` were proved against *relational* specs (`ParseOk`, "everything
before `k` is `< x`"). Here each gets a plain-function reference (`parseRef`, `lowerBoundRef`),
tested against an independent oracle, and a refinement theorem that says the C function returns
*exactly* what the reference computes. The refinement theorems are corollaries of the existing
proofs; the reference is what a reviewer reads.
-/

open LC LC.Check

namespace Examples.Refinement

/-! ## `parse_u32` -/

namespace Parse
open Examples.ParseU32

def isDigitB (c : BitVec 8) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- **The reference for `parse_u32`**: `some` value exactly when the input is a non-empty run
of ASCII digits whose value fits in 32 bits. -/
def parseRef (cs : List (BitVec 8)) : Option Nat :=
  if !cs.isEmpty && cs.all isDigitB && decVal cs < 2 ^ 32 then some (decVal cs) else none

def ofString (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat
def toString' (cs : List (BitVec 8)) : String := String.ofList (cs.map fun c => Char.ofNat c.toNat)

#guard parseRef (ofString "0") = some 0
#guard parseRef (ofString "007") = some 7                     -- leading zeros are fine
#guard parseRef (ofString "4294967295") = some 4294967295     -- UINT32_MAX
#guard parseRef (ofString "4294967296") = none
#guard parseRef (ofString "") = none
#guard parseRef (ofString "+1") = none
#guard parseRef (ofString " 1") = none

/-- Mostly digits, sometimes other bytes, lengths up to 12 (so some overflow). -/
def genDigits : Gen (List (BitVec 8)) :=
  Gen.list 12 (Gen.frequency [
    (12, do return BitVec.ofNat 8 (48 + (← Gen.below 10))),
    (1, Gen.elements (ofString "+- a/:_")),
    (1, Gen.bv 8)])

/-- The oracle: Lean's own `String.toNat?`, plus the 32-bit limit.

Testing against it found one disagreement: `"1_000".toNat? = some 1000`, because Lean allows
`_` as a digit separator, and C-style parsing doesn't. The oracle has to exclude it. A spec
reviewed only by reading could easily have copied that behaviour, or missed it. -/
def oracle (cs : List (BitVec 8)) : Option Nat :=
  if cs.any (· == 95) then none                               -- '_'
  else match (toString' cs).toNat? with
    | some n => if n < 2 ^ 32 then some n else none
    | none => none

#guard "1_000".toNat? = some 1000 && parseRef (ofString "1_000") = none
#guard forAll genDigits fun cs => parseRef cs == oracle cs
#guard (samples genDigits).any (parseRef · |>.isSome) && (samples genDigits).any (parseRef · |>.isNone)

/-- Run `parse_u32` in the interpreter: the result, and what was written to `out[0]`. -/
def runParse (cs : List (BitVec 8)) : Option (Option Nat) :=
  let cells := u8s cs
  match parseU32.callMem [.ptr .u8 ⟨0, 0⟩, .u32 cs.length, .ptr .u32 ⟨1, 0⟩]
      [(0, if cells.isEmpty then [.u8 0] else cells), (1, [.u32 0])] (P := prog) with
  | .ok (.bool true, m) => match m.read 1 0 with
    | some (.int .u32 k) => some (some k.toNat)
    | _ => none
  | .ok (.bool false, _) => some none
  | _ => none

#guard forAll genDigits fun cs => runParse cs == some (parseRef cs)

theorem parseRef_cond (cs : List (BitVec 8)) :
    (!cs.isEmpty && cs.all isDigitB && decide (decVal cs < 2 ^ 32)) = true ↔ ParseOk cs := by
  simp [ParseOk, IsDigit, isDigitB, and_assoc]

theorem parseRef_of_ok {cs : List (BitVec 8)} (h : ParseOk cs) : parseRef cs = some (decVal cs) := by
  simp only [parseRef, (parseRef_cond cs).mpr h, ite_true]

theorem parseRef_of_not_ok {cs : List (BitVec 8)} (h : ¬ ParseOk cs) : parseRef cs = none := by
  unfold parseRef
  rw [(Bool.not_eq_true _).mp fun e => h ((parseRef_cond cs).mp e)]; rfl

/-- **`parse_u32` refines `parseRef`.** It returns `true` exactly when `parseRef cs` is `some`,
and `out[0]` then holds that value; otherwise `out[0]` keeps its old contents `w`. -/
theorem parseU32_refines (P : Program) (hP : P.find? "is_digit" = some isDigit)
    (p o : Ptr) (cs : List (BitVec 8)) (w : Val) (hlen : cs.length < 2 ^ 32)
    (h hf : Heap) (m : Mem) (hpre : (array p (u8s cs) ∗ array o [w]) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m' h', parseU32.Returns P [.ptr .u8 p, .u32 cs.length, .ptr .u32 o] m
        (.bool (parseRef cs).isSome) m' ∧ h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      (array p (u8s cs) ∗ array o [((parseRef cs).map nu32).getD w]) h' := by
  obtain ⟨v, m', h', hret, d', hm', hpost⟩ := parseU32_correct P hP p o cs w hlen h hf m hpre d hm
  rcases hpost with ⟨hok, rfl, harr⟩ | ⟨hok, rfl, rfl⟩
  · rw [parseRef_of_ok hok]; exact ⟨m', h', hret, d', hm', harr⟩
  · rw [parseRef_of_not_ok hok]; exact ⟨m', h', hret, d', hm', hpre⟩

end Parse

/-! ## `lower_bound` -/

namespace LowerBound
open Examples.Search Examples.SpecFirst

/-- **The reference for `lower_bound`**: the length of the run of elements `< x` at the front. -/
def lowerBoundRef (xs : List (BitVec 32)) (x : BitVec 32) : Nat :=
  (xs.takeWhile (·.toNat < x.toNat)).length

#guard lowerBoundRef [5, 7, 7, 9] 7 = 1
#guard lowerBoundRef [5, 7, 7, 9] 8 = 3
#guard lowerBoundRef [5, 7, 7, 9] 100 = 4
#guard lowerBoundRef [] 7 = 0

def genSorted : Gen (List (BitVec 32) × BitVec 32) := do
  return (← Gen.sortedList 10 (Gen.bvSmall 32), ← Gen.bvSmall 32)

-- Oracle: on a sorted list, it's the number of elements `< x`, wherever they are.
#guard forAll genSorted fun (xs, x) => lowerBoundRef xs x == (xs.filter (·.toNat < x.toNat)).length
-- The precondition matters: on unsorted lists the two differ, and binary search can't count.
#guard (samples (do return (← Gen.list 10 (Gen.bvSmall 32), ← Gen.bvSmall 32))).any
  fun (xs, x) => lowerBoundRef xs x != (xs.filter (·.toNat < x.toNat)).length

def runLowerBound (xs : List (BitVec 32)) (x : BitVec 32) : Option Nat :=
  let cells := u32s xs
  match lowerBound.callMem [.ptr .u32 ⟨0, 0⟩, .u32 xs.length, .int .u32 x]
      [(0, if cells.isEmpty then [.u32 0] else cells)] with
  | .ok (.int .u32 k, _) => some k.toNat
  | _ => none

#guard forAll genSorted fun (xs, x) => runLowerBound xs x == some (lowerBoundRef xs x)

/-- The executable precondition `SortedRef` (from `is_sorted`'s spec) is the `Sorted` that
`lower_bound`'s proof assumes. So callers can *check* it, with the verified `is_sorted`. -/
theorem sorted_of_sortedRef {xs : List (BitVec 32)} (hs : SortedRef xs) : Sorted xs := by
  intro i j a b hij ha hb
  rw [List.getElem?_eq_some_iff] at ha hb
  obtain ⟨hi, rfl⟩ := ha
  obtain ⟨hj, rfl⟩ := hb
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · exact List.pairwise_iff_getElem.mp hs i j hi hj hlt
  · exact Nat.le_refl _

/-- A split point of the list is the length of its `takeWhile`. -/
theorem takeWhile_length_of_split {α} {p : α → Bool} :
    ∀ {xs : List α} {k : Nat}, k ≤ xs.length →
      (∀ j a, j < k → xs[j]? = some a → p a = true) →
      (∀ j a, k ≤ j → xs[j]? = some a → p a = false) →
      (xs.takeWhile p).length = k
  | [], k, hk, _, _ => by simp at hk; simp [hk]
  | y :: ys, 0, _, _, habove => by simp [habove 0 y (Nat.le_refl _) rfl]
  | y :: ys, k + 1, hk, hbelow, habove => by
    simp only [List.takeWhile_cons, hbelow 0 y (by omega) rfl, ite_true, List.length_cons]
    congr 1
    exact takeWhile_length_of_split (by simp at hk; omega)
      (fun j a hj ha => hbelow (j + 1) a (by omega) (by simpa using ha))
      (fun j a hj ha => habove (j + 1) a (by omega) (by simpa using ha))

/-- **`lower_bound` refines `lowerBoundRef`** on every sorted array (in the executable sense of
`SortedRef`). -/
theorem lowerBound_refines (P : Program) (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32)
    (hlen : xs.length < 2 ^ 32) (hs : SortedRef xs) (h hf : Heap) (m : Mem)
    (ha : array p (u32s xs) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m', lowerBound.Returns P [.ptr .u32 p, .u32 xs.length, .int .u32 x] m
        (nu32 (lowerBoundRef xs x)) m' ∧ m'.heap = m.heap := by
  obtain ⟨k, m', hret, hm', hk, hbelow, habove⟩ :=
    lowerBound_correct P p xs x hlen (sorted_of_sortedRef hs) h hf m ha d hm
  have : lowerBoundRef xs x = k := takeWhile_length_of_split hk
    (fun j a hj hja => by simpa using hbelow j a hj hja)
    (fun j a hj hja => by simpa using habove j a hj hja)
  exact ⟨m', this ▸ hret, hm'⟩

end LowerBound

end Examples.Refinement

#print axioms Examples.Refinement.Parse.parseU32_refines
#print axioms Examples.Refinement.LowerBound.lowerBound_refines
