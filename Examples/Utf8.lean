import LC

/-!
# UTF-8 validation: `utf8_valid`

```c
bool utf8_valid(const uint8_t *p, uint32_t n);   // the n bytes at p are well-formed UTF-8
```

The reference is Unicode Table 3-7 (well-formed byte sequences), read literally: each lead
byte names the ranges its continuation bytes must fall in. The code is the usual one-byte-at-a-
time automaton: `need` continuation bytes are still expected, and the next one must be in
`lo..hi`. The proof shows the automaton accepts exactly the inputs the table accepts; its
invariant is "the whole input is valid iff the rest of it, read from the automaton's state, is".
-/

open LC LC.Check

namespace Examples.Utf8

/-! ## 1. The reference -/

/-- Unicode Table 3-7: the ranges of the continuation bytes a lead byte `b` requires, or `none`
if `b` can't start a sequence (`80..C1`, `F5..FF`). -/
def conts (b : Nat) : Option (List (Nat × Nat)) :=
  if b ≤ 0x7F then some []
  else if 0xC2 ≤ b ∧ b ≤ 0xDF then some [(0x80, 0xBF)]
  else if b = 0xE0 then some [(0xA0, 0xBF), (0x80, 0xBF)]
  else if 0xE1 ≤ b ∧ b ≤ 0xEC then some [(0x80, 0xBF), (0x80, 0xBF)]
  else if b = 0xED then some [(0x80, 0x9F), (0x80, 0xBF)]                 -- no surrogates
  else if 0xEE ≤ b ∧ b ≤ 0xEF then some [(0x80, 0xBF), (0x80, 0xBF)]
  else if b = 0xF0 then some [(0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)]
  else if 0xF1 ≤ b ∧ b ≤ 0xF3 then some [(0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)]
  else if b = 0xF4 then some [(0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)]    -- ≤ U+10FFFF
  else none

/-- Consume one byte per range from the front of `r`; the rest, or `none` on a mismatch or
if `r` runs out. -/
def matchConts : List (Nat × Nat) → List (BitVec 8) → Option (List (BitVec 8))
  | [], r => some r
  | _ :: _, [] => none
  | (lo, hi) :: cs, c :: r => if lo ≤ c.toNat ∧ c.toNat ≤ hi then matchConts cs r else none

theorem matchConts_length {cs : List (Nat × Nat)} {r r' : List (BitVec 8)}
    (h : matchConts cs r = some r') : r'.length ≤ r.length := by
  induction cs generalizing r with
  | nil => simp [matchConts] at h; subst h; exact Nat.le_refl _
  | cons c cs ih =>
    obtain ⟨lo, hi⟩ := c
    cases r with
    | nil => simp [matchConts] at h
    | cons x r =>
      simp only [matchConts] at h
      split at h
      · have := ih h; simp; omega
      · simp at h

/-- **The specification**: `xs` is a sequence of well-formed code-unit sequences (Table 3-7). -/
def validRef (xs : List (BitVec 8)) : Bool :=
  match xs with
  | [] => true
  | b :: r =>
    match conts b.toNat with
    | none => false
    | some cs =>
      match _h : matchConts cs r with
      | none => false
      | some r' => validRef r'
termination_by xs.length
decreasing_by have := matchConts_length _h; simp; omega

/-! ## 2. Test the reference -/

def bytes (xs : List Nat) : List (BitVec 8) := xs.map (BitVec.ofNat 8)

#guard validRef []
#guard validRef (bytes [0x41, 0x7F, 0x00])
#guard validRef (bytes [0xC2, 0x80, 0xDF, 0xBF])                  -- U+0080, U+07FF
#guard validRef (bytes [0xE0, 0xA0, 0x80, 0xEF, 0xBF, 0xBF])      -- U+0800, U+FFFF
#guard validRef (bytes [0xED, 0x9F, 0xBF, 0xEE, 0x80, 0x80])      -- U+D7FF, U+E000
#guard validRef (bytes [0xF0, 0x90, 0x80, 0x80, 0xF4, 0x8F, 0xBF, 0xBF])  -- U+10000, U+10FFFF
#guard !validRef (bytes [0xC0, 0x80])                              -- overlong
#guard !validRef (bytes [0xC1, 0xBF])
#guard !validRef (bytes [0xE0, 0x9F, 0xBF])                        -- overlong
#guard !validRef (bytes [0xF0, 0x8F, 0xBF, 0xBF])                  -- overlong
#guard !validRef (bytes [0xED, 0xA0, 0x80])                        -- surrogate U+D800
#guard !validRef (bytes [0xED, 0xBF, 0xBF])                        -- surrogate U+DFFF
#guard !validRef (bytes [0xF4, 0x90, 0x80, 0x80])                  -- U+110000
#guard !validRef (bytes [0xF5, 0x80, 0x80, 0x80])
#guard !validRef (bytes [0xFF])
#guard !validRef (bytes [0x80])                                    -- stray continuation
#guard !validRef (bytes [0x41, 0xBF])
#guard !validRef (bytes [0xE2, 0x82])                              -- truncated
#guard !validRef (bytes [0xF0, 0x9F, 0x98])
#guard !validRef (bytes [0xC2, 0x41])                              -- non-continuation

/-- Lean's own validator, an independent implementation. -/
def oracle (xs : List (BitVec 8)) : Bool :=
  ByteArray.validateUTF8 ⟨(xs.map fun b => b.toNat.toUInt8).toArray⟩

/-- Scalar values near every boundary of the table. -/
def genChar : Gen Char := do
  let c ← Gen.frequency [
    (2, Gen.range 0 0x7F), (1, Gen.range 0x80 0x7FF), (1, Gen.range 0x800 0xD7FF),
    (1, Gen.range 0xE000 0xFFFF), (1, Gen.range 0x10000 0x10FFFF),
    (2, Gen.elements [0x7F, 0x80, 0x7FF, 0x800, 0xD7FF, 0xE000, 0xFFFF, 0x10000, 0x10FFFF])]
  return Char.ofNat c

/-- Encoded text, sometimes with one byte replaced or the end cut off. -/
def genBytes : Gen (List (BitVec 8)) := do
  let cs ← Gen.list 5 genChar
  let bs := (cs.flatMap String.utf8EncodeChar).map fun u => BitVec.ofNat 8 u.toNat
  match ← Gen.below 4 with
  | 0 => return bs
  | 1 => return bs.take (← Gen.below (bs.length + 1))
  | 2 => do
    let k ← Gen.below (bs.length + 1)
    let b ← Gen.frequency [(1, Gen.bv 8), (1, Gen.elements (bytes
      [0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xC1, 0xC2, 0xE0, 0xED, 0xF0, 0xF4, 0xF5]))]
    return bs.take k ++ [b] ++ bs.drop (k + 1)
  | _ => Gen.list 6 (Gen.bv 8)

#guard forAll genBytes (n := 1000) fun xs => validRef xs == oracle xs
-- Encoding any scalar values gives valid UTF-8.
#guard forAll (Gen.list 5 genChar) fun cs =>
  validRef ((cs.flatMap String.utf8EncodeChar).map fun u => BitVec.ofNat 8 u.toNat)
-- Validity is closed under concatenation.
#guard forAll (do return (← genBytes, ← genBytes)) fun (a, b) =>
  !(validRef a && validRef b) || validRef (a ++ b)
#guard (samples genBytes).any validRef && (samples genBytes).any (! validRef ·)

/-! ## 3. The code

```c
bool utf8_valid(const uint8_t *p, uint32_t n) {
  uint32_t i = 0u, need = 0u;
  uint8_t lo = 0x80, hi = 0xBF, b;
  while (i < n) {
    b = p[i];
    if (need == 0u) {
      if (b < 0x80) {}
      else if (b < 0xC2) return false;
      else if (b < 0xE0) { need = 1u; lo = 0x80; hi = 0xBF; }
      else if (b < 0xF0) { need = 2u; lo = 0x80; hi = 0xBF;
                           if (b == 0xE0) lo = 0xA0; if (b == 0xED) hi = 0x9F; }
      else if (b < 0xF5) { need = 3u; lo = 0x80; hi = 0xBF;
                           if (b == 0xF0) lo = 0x90; if (b == 0xF4) hi = 0x8F; }
      else return false;
    } else {
      if (b < lo) return false;
      if (b > hi) return false;
      need = need - 1u; lo = 0x80; hi = 0xBF;
    }
    i = i + 1u;
  }
  return need == 0u;
}
```
-/

def utf8Valid : Fn where
  name   := "utf8_valid"
  params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("need", .int .u32), ("lo", .int .u8), ("hi", .int .u8),
             ("b", .int .u8)]
  body   := .block [
    "i" ::= .u32 0,
    "need" ::= .u32 0,
    "lo" ::= .u8 0x80,
    "hi" ::= .u8 0xBF,
    .while (v "i" <. v "n") (.block [
      .load "b" (v "p") (v "i"),
      .ite (v "need" ==. .u32 0)
        (.ite (v "b" <. .u8 0x80) .skip
          (.ite (v "b" <. .u8 0xC2) (.ret .ff)
            (.ite (v "b" <. .u8 0xE0)
              (.block ["need" ::= .u32 1, "lo" ::= .u8 0x80, "hi" ::= .u8 0xBF])
              (.ite (v "b" <. .u8 0xF0)
                (.block ["need" ::= .u32 2, "lo" ::= .u8 0x80, "hi" ::= .u8 0xBF,
                  .ite (v "b" ==. .u8 0xE0) ("lo" ::= .u8 0xA0) .skip,
                  .ite (v "b" ==. .u8 0xED) ("hi" ::= .u8 0x9F) .skip])
                (.ite (v "b" <. .u8 0xF5)
                  (.block ["need" ::= .u32 3, "lo" ::= .u8 0x80, "hi" ::= .u8 0xBF,
                    .ite (v "b" ==. .u8 0xF0) ("lo" ::= .u8 0x90) .skip,
                    .ite (v "b" ==. .u8 0xF4) ("hi" ::= .u8 0x8F) .skip])
                  (.ret .ff))))))
        (.block [
          .ite (v "b" <. v "lo") (.ret .ff) .skip,
          .ite (v "b" >. v "hi") (.ret .ff) .skip,
          "need" ::= v "need" - .u32 1,
          "lo" ::= .u8 0x80,
          "hi" ::= .u8 0xBF]),
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .bool
  result := v "need" ==. .u32 0

#guard utf8Valid.typeCheck
#guard (cTranslationUnit [utf8Valid]).isOk

/-! ## 4. Test the code against the reference -/

def runUtf8 (xs : List (BitVec 8)) : Option Bool :=
  let cells := u8s xs
  match utf8Valid.callMem [.ptr .u8 ⟨0, 0⟩, .u32 xs.length]
      [(0, if cells.isEmpty then [.u8 0] else cells)] with
  | .ok (.bool b, _) => some b
  | _ => none

#guard forAll genBytes (n := 1000) fun xs => runUtf8 xs == some (validRef xs)

/-! ## 5. The proof: `utf8_valid` refines `validRef` -/

/-- Validity of what's left, `r`, after the ranges `cs` (the pending continuation bytes). -/
def pendRef (cs : List (Nat × Nat)) (r : List (BitVec 8)) : Bool :=
  match matchConts cs r with
  | none => false
  | some r' => validRef r'

/-- The automaton's state as the ranges still expected: `need` bytes, the first in `lo..hi`. -/
def stateConts : Nat → BitVec 8 → BitVec 8 → List (Nat × Nat)
  | 0, _, _ => []
  | k + 1, lo, hi => (lo.toNat, hi.toNat) :: List.replicate k (0x80, 0xBF)

def utf8Inv (p : Ptr) (xs : List (BitVec 8)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i k lo hi, i ≤ xs.length ∧ k ≤ 3 ∧ st.get "p" = some (.ptr .u8 p) ∧
    st.get "n" = some (nu32 xs.length) ∧ st.get "i" = some (nu32 i) ∧
    st.get "need" = some (nu32 k) ∧ st.get "lo" = some (.int .u8 lo) ∧
    st.get "hi" = some (.int .u8 hi) ∧
    validRef xs = pendRef (stateConts k lo hi) (xs.drop i) ∧ h = h₀

/-! ### Unfolding the reference one byte at a time -/

theorem pendRef_nil (r : List (BitVec 8)) : pendRef [] r = validRef r := by
  simp [pendRef, matchConts]

theorem pendRef_cons_nil (c : Nat × Nat) (cs : List (Nat × Nat)) : pendRef (c :: cs) [] = false := by
  simp [pendRef, matchConts]

theorem pendRef_cons_cons (lo hi : Nat) (cs : List (Nat × Nat)) (x : BitVec 8) (r : List (BitVec 8)) :
    pendRef ((lo, hi) :: cs) (x :: r) =
      if lo ≤ x.toNat ∧ x.toNat ≤ hi then pendRef cs r else false := by
  by_cases h : lo ≤ x.toNat ∧ x.toNat ≤ hi <;> simp [pendRef, matchConts, h]

theorem validRef_cons (b : BitVec 8) (r : List (BitVec 8)) :
    validRef (b :: r) = match conts b.toNat with
      | none => false
      | some cs => pendRef cs r := by
  rw [validRef]
  cases conts b.toNat with
  | none => rfl
  | some cs => simp only [pendRef]; split <;> simp_all

theorem stateConts_80_BF (k : Nat) : stateConts k 128#8 191#8 = List.replicate k (0x80, 0xBF) := by
  cases k <;> rfl

/-! ### The lead byte (`need == 0`) -/

theorem lead_step {xs : List (BitVec 8)} {i : Nat} {lo hi lo' hi' : BitVec 8} {k : Nat}
    (hil : i < xs.length) (hinv : validRef xs = pendRef (stateConts 0 lo hi) (xs.drop i))
    (hc : conts xs[i].toNat = some (stateConts k lo' hi')) :
    validRef xs = pendRef (stateConts k lo' hi') (xs.drop (i + 1)) := by
  rw [hinv, List.drop_eq_getElem_cons hil, stateConts, pendRef_nil, validRef_cons, hc]

theorem lead_bad {xs : List (BitVec 8)} {i : Nat} {lo hi : BitVec 8}
    (hil : i < xs.length) (hinv : validRef xs = pendRef (stateConts 0 lo hi) (xs.drop i))
    (hc : conts xs[i].toNat = none) : validRef xs = false := by
  rw [hinv, List.drop_eq_getElem_cons hil, stateConts, pendRef_nil, validRef_cons, hc]

/-- Table 3-7 row by row, in the form the code's tests give. -/
macro "conts_tac" : tactic => `(tactic| (
  unfold conts
  repeat' (first | rfl | omega | split)))

theorem toNat_ne {b : BitVec 8} {c : Nat} (h : ¬ b = BitVec.ofNat 8 c) (hc : c < 256) :
    b.toNat ≠ c := by intro e; apply h; apply BitVec.eq_of_toNat_eq; simp; omega

theorem toNat_eq {b : BitVec 8} {c : Nat} (h : b = BitVec.ofNat 8 c) (hc : c < 256) :
    b.toNat = c := by subst h; simp; omega

theorem conts_ascii {b lo hi : BitVec 8} (h : b.toNat < 128) :
    conts b.toNat = some (stateConts 0 lo hi) := by conts_tac
theorem conts_bad1 {b : BitVec 8} (h1 : 128 ≤ b.toNat) (h2 : b.toNat < 194) :
    conts b.toNat = none := by conts_tac
theorem conts_bad2 {b : BitVec 8} (h : 245 ≤ b.toNat) : conts b.toNat = none := by conts_tac
theorem conts_2 {b : BitVec 8} (h1 : 194 ≤ b.toNat) (h2 : b.toNat < 224) :
    conts b.toNat = some (stateConts 1 128#8 191#8) := by conts_tac
theorem conts_E0 {b : BitVec 8} (h : b = 224#8) :
    conts b.toNat = some (stateConts 2 160#8 191#8) := by subst h; rfl
theorem conts_ED {b : BitVec 8} (h : b = 237#8) :
    conts b.toNat = some (stateConts 2 128#8 159#8) := by subst h; rfl
theorem conts_3 {b : BitVec 8} (h1 : 224 ≤ b.toNat) (h2 : b.toNat < 240) (h3 : ¬ b = 224#8)
    (h4 : ¬ b = 237#8) : conts b.toNat = some (stateConts 2 128#8 191#8) := by
  have := toNat_ne h3 (by omega); have := toNat_ne h4 (by omega); conts_tac
theorem conts_F0 {b : BitVec 8} (h : b = 240#8) :
    conts b.toNat = some (stateConts 3 144#8 191#8) := by subst h; rfl
theorem conts_F4 {b : BitVec 8} (h : b = 244#8) :
    conts b.toNat = some (stateConts 3 128#8 143#8) := by subst h; rfl
theorem conts_4 {b : BitVec 8} (h1 : 240 ≤ b.toNat) (h2 : b.toNat < 245) (h3 : ¬ b = 240#8)
    (h4 : ¬ b = 244#8) : conts b.toNat = some (stateConts 3 128#8 191#8) := by
  have := toNat_ne h3 (by omega); have := toNat_ne h4 (by omega); conts_tac

/-! ### A continuation byte (`need > 0`) -/

theorem cont_lo {xs : List (BitVec 8)} {i k : Nat} {lo hi : BitVec 8}
    (hil : i < xs.length) (hinv : validRef xs = pendRef (stateConts k lo hi) (xs.drop i))
    (hk : ¬ k = 0) (h : xs[i].toNat < lo.toNat) : validRef xs = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hinv, List.drop_eq_getElem_cons hil, stateConts, pendRef_cons_cons, ite_eq_right (by omega), Bool.false_eq]

theorem cont_hi {xs : List (BitVec 8)} {i k : Nat} {lo hi : BitVec 8}
    (hil : i < xs.length) (hinv : validRef xs = pendRef (stateConts k lo hi) (xs.drop i))
    (hk : ¬ k = 0) (h : hi.toNat < xs[i].toNat) : validRef xs = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hinv, List.drop_eq_getElem_cons hil, stateConts, pendRef_cons_cons, ite_eq_right (by omega), Bool.false_eq]

theorem cont_ok {xs : List (BitVec 8)} {i k : Nat} {lo hi : BitVec 8}
    (hil : i < xs.length) (hinv : validRef xs = pendRef (stateConts k lo hi) (xs.drop i))
    (hk : ¬ k = 0) (h1 : lo.toNat ≤ xs[i].toNat) (h2 : xs[i].toNat ≤ hi.toNat) :
    validRef xs = pendRef (stateConts (k - 1) 128#8 191#8) (xs.drop (i + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [hinv, List.drop_eq_getElem_cons hil, stateConts, pendRef_cons_cons, ite_eq_left ⟨h1, h2⟩,
    Nat.add_sub_cancel, stateConts_80_BF]

/-! ### The end of the input -/

theorem exit_ok {xs : List (BitVec 8)} {k : Nat} {lo hi : BitVec 8} (hk : k ≤ 3)
    (hinv : validRef xs = pendRef (stateConts k lo hi) (xs.drop xs.length)) :
    decide (k = 0) = validRef xs := by
  rw [hinv, List.drop_length]
  cases k with
  | zero => simp [stateConts, pendRef_nil, validRef]
  | succ j => rw [stateConts, pendRef_cons_nil]; simp

theorem utf8Valid_refines (P : Program) (p : Ptr) (xs : List (BitVec 8))
    (hlen : xs.length < 2 ^ 32) (h hf : Heap) (m : Mem) (ha : array p (u8s xs) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m', utf8Valid.Returns P [.ptr .u8 p, .u32 xs.length] m (.bool (validRef xs)) m' ∧
      m'.heap = m.heap := by
  have hinit : utf8Valid.initStore [.ptr .u8 p, .u32 xs.length] =
      some [("p", .ptr .u8 p), ("n", nu32 xs.length)] := by
    simp [Fn.initStore, utf8Valid, Store.empty]; constructor <;> rfl
  suffices hbody : swpo P utf8Valid.body (fun o st h' => ∃ v, utf8Valid.finish o st = some v ∧
      (v = .bool (validRef xs) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swpo
      (post := fun v h' => v = .bool (validRef xs) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (utf8Inv p xs h) (counterVariant xs.length) [utf8Inv, counterVariant]
  · exact lead_step ‹_› ‹_› (conts_ascii ‹_›)
  · exact lead_bad ‹_› ‹_› (conts_bad1 ‹_› ‹_›)
  · exact lead_step ‹_› ‹_› (conts_2 ‹_› ‹_›)
  · exact lead_step ‹_› ‹_› (conts_E0 ‹_›)
  · exact lead_step ‹_› ‹_› (conts_ED ‹_›)
  · exact lead_step ‹_› ‹_› (conts_3 ‹_› ‹_› ‹_› ‹_›)
  · exact lead_step ‹_› ‹_› (conts_F0 ‹_›)
  · exact lead_step ‹_› ‹_› (conts_F4 ‹_›)
  · exact lead_step ‹_› ‹_› (conts_4 ‹_› ‹_› ‹_› ‹_›)
  · exact lead_bad ‹_› ‹_› (conts_bad2 ‹_›)
  · exact cont_lo ‹_› ‹_› ‹_› ‹_›
  · exact cont_hi ‹_› ‹_› ‹_› ‹_›
  · exact cont_ok ‹_› ‹_› ‹_› ‹_› ‹_›
  · exact exit_ok ‹_› ‹_›

end Examples.Utf8

#print axioms Examples.Utf8.utf8Valid_refines
