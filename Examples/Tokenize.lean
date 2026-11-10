import LC

/-!
# `tokenize`: split a byte buffer into whitespace-separated tokens

```c
uint32_t tokenize(const uint8_t *p, uint32_t n, uint32_t *starts, uint32_t *lens, uint32_t cap);
```

A token is a maximal non-empty run of bytes other than space, tab, newline and carriage return.
`tokenize` returns the number of tokens and writes the offset and length of the first
`min(count, cap)` of them to `starts` and `lens`, leaving the other entries alone.

The reference (`tokensRef`) is declarative: a token starts at every non-whitespace byte that is
first or follows whitespace, and runs for as long as the bytes are not whitespace. The code is a
one-pass state machine. The proof's one real lemma (`tokensRef_snoc`) says how the token list of
a prefix changes when one byte is appended.
-/

open LC LC.Check

namespace Examples.Tokenize

/-! ## 1. The reference -/

/-- Whitespace: exactly space, tab, newline and carriage return. -/
def isWs (c : BitVec 8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

/-- A token starts at `s` when byte `s` is not whitespace and is either the first byte or
follows a whitespace byte. -/
def startsAt (xs : List (BitVec 8)) (s : Nat) : Bool :=
  xs[s]?.any (fun c => !isWs c) && (s == 0 || xs[s - 1]?.any isWs)

/-- The length of the run of non-whitespace bytes starting at `s`. -/
def runLen (xs : List (BitVec 8)) (s : Nat) : Nat :=
  ((xs.drop s).takeWhile (fun c => !isWs c)).length

/-- The tokens, in order, as `(start, length)` pairs. -/
def tokensRef (xs : List (BitVec 8)) : List (Nat × Nat) :=
  ((List.range xs.length).filter (startsAt xs)).map fun s => (s, runLen xs s)

/-- What an output array holds afterwards: its original contents `orig` (length `cap`), with
the first `min(vals.length, cap)` entries replaced by `vals`. -/
def fill (orig : List (BitVec 32)) (vals : List Nat) : List (BitVec 32) :=
  (vals.map (BitVec.ofNat 32)).take orig.length ++ orig.drop vals.length

/-! ## 2. Test the reference -/

def bytes (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat

#guard tokensRef (bytes "  ab c\n") = [(2, 2), (5, 1)]          -- the example from the task
#guard tokensRef [] = []
#guard tokensRef (bytes " \t\r\n ") = []
#guard tokensRef (bytes "abc") = [(0, 3)]
#guard tokensRef (bytes "a\tb\rc\nd e") = [(0, 1), (2, 1), (4, 1), (6, 1), (8, 1)]
#guard tokensRef [0, 11, 12, 255] = [(0, 4)]                     -- NUL, VT, FF are not whitespace
#guard fill [7, 7] [1, 2, 3] = [1, 2]
#guard fill [7, 7, 7] [1] = [1, 7, 7]
#guard fill [] [1] = []

/-- An independent oracle: a left-to-right scan with an explicit "current token" state. -/
def scanOracle (xs : List (BitVec 8)) : List (Nat × Nat) :=
  let (done, cur) := xs.zipIdx.foldl (fun (acc : List (Nat × Nat) × Option (Nat × Nat)) (c, i) =>
    match acc.2, isWs c with
    | none, true => acc
    | none, false => (acc.1, some (i, 1))
    | some t, true => (acc.1 ++ [t], none)
    | some (s, l), false => (acc.1, some (s, l + 1))) ([], none)
  done ++ cur.toList

def genBytes : Gen (List (BitVec 8)) :=
  Gen.list 12 (Gen.frequency [(1, Gen.elements [32, 9, 10, 13]), (1, Gen.elements [97, 98, 0, 255]),
    (1, Gen.bv 8)])

#guard forAll genBytes fun xs => tokensRef xs == scanOracle xs
-- Algebraic laws: the tokens' bytes are exactly the non-whitespace bytes, each token is
-- non-empty and maximal, and tokens are separated.
#guard forAll genBytes fun xs =>
  ((tokensRef xs).flatMap fun (s, l) => (xs.drop s).take l) == xs.filter (fun c => !isWs c)
#guard forAll genBytes fun xs => (tokensRef xs).all fun (s, l) =>
  0 < l && ((xs.drop s).take l).all (fun c => !isWs c) && (xs[s + l]?.all isWs) &&
    (s == 0 || xs[s - 1]?.all isWs)
#guard (samples genBytes).any (fun xs => (tokensRef xs).length ≥ 3) &&
  (samples genBytes).any (fun xs => (tokensRef xs).length == 0 && xs.length > 0)

/-! ## 3. The code

```c
uint32_t tokenize(const uint8_t *p, uint32_t n, uint32_t *starts, uint32_t *lens, uint32_t cap) {
  uint32_t i = 0u, cnt = 0u, st = 0u; bool in = false; uint8_t c;
  while (i < n) {
    c = p[i];
    if (c == 32 || c == 9 || c == 10 || c == 13) {
      if (in) {
        if (cnt < cap) { starts[cnt] = st; lens[cnt] = i - st; }
        cnt = cnt + 1u; in = false;
      }
    } else if (!in) { st = i; in = true; }
    i = i + 1u;
  }
  if (in) { if (cnt < cap) { starts[cnt] = st; lens[cnt] = i - st; } cnt = cnt + 1u; }
  return cnt;
}
```
-/

def tokenize : Fn where
  name   := "tokenize"
  params := [("p", .ptr .u8), ("n", .int .u32), ("starts", .ptr .u32), ("lens", .ptr .u32),
             ("cap", .int .u32)]
  locals := [("i", .int .u32), ("cnt", .int .u32), ("st", .int .u32), ("intok", .bool),
             ("c", .int .u8)]
  body   := .block [
    "i" ::= .u32 0,
    "cnt" ::= .u32 0,
    "st" ::= .u32 0,
    "intok" ::= .ff,
    .while (v "i" <. v "n") (.block [
      .load "c" (v "p") (v "i"),
      .ite (v "c" ==. .u8 32 ||. v "c" ==. .u8 9 ||. v "c" ==. .u8 10 ||. v "c" ==. .u8 13)
        (.ite (v "intok")
          (.block [
            .ite (v "cnt" <. v "cap")
              (.block [.store (v "starts") (v "cnt") (v "st"),
                       .store (v "lens") (v "cnt") (v "i" - v "st")])
              .skip,
            "cnt" ::= v "cnt" + .u32 1,
            "intok" ::= .ff])
          .skip)
        (.ite (v "intok") .skip (.block ["st" ::= v "i", "intok" ::= .tt])),
      "i" ::= v "i" + .u32 1
    ]),
    .ite (v "intok")
      (.block [
        .ite (v "cnt" <. v "cap")
          (.block [.store (v "starts") (v "cnt") (v "st"),
                   .store (v "lens") (v "cnt") (v "i" - v "st")])
          .skip,
        "cnt" ::= v "cnt" + .u32 1])
      .skip
  ]
  ret    := .int .u32
  result := v "cnt"

#guard tokenize.typeCheck
#guard (cTranslationUnit [tokenize]).isOk

/-! ## 4. Test the code against the reference

The output arrays get one extra sentinel cell past `cap`, to catch writes beyond it. -/

def runTokenize (xs : List (BitVec 8)) (cap : Nat) : Option (Nat × List Val × List Val) :=
  let cells := u8s xs
  let out := u32s (List.replicate (cap + 1) 7)
  match tokenize.callMem [.ptr .u8 ⟨0, 0⟩, .u32 xs.length, .ptr .u32 ⟨1, 0⟩, .ptr .u32 ⟨2, 0⟩,
      .u32 cap] [(0, if cells.isEmpty then [.u8 0] else cells), (1, out), (2, out)] with
  | .ok (.int .u32 r, m) => some (r.toNat, (m.lookup 1).getD [], (m.lookup 2).getD [])
  | _ => none

def expected (xs : List (BitVec 8)) (cap : Nat) : Option (Nat × List Val × List Val) :=
  let ts := tokensRef xs
  let orig := List.replicate cap 7
  some (ts.length, u32s (fill orig (ts.map (·.1)) ++ [7]), u32s (fill orig (ts.map (·.2)) ++ [7]))

#guard runTokenize (bytes "  ab c\n") 1 = some (2, [.u32 2, .u32 7], [.u32 2, .u32 7])
#guard forAll (do return (← genBytes, ← Gen.below 5)) fun (xs, cap) =>
  runTokenize xs cap == expected xs cap

/-! ## 5. The proof -/


def bump (n : Nat) (c : BitVec 8) (t : Nat × Nat) : Nat × Nat :=
  if t.1 + t.2 = n ∧ isWs c = false then (t.1, t.2 + 1) else t

theorem runLen_snoc (ys : List (BitVec 8)) (c : BitVec 8) (s : Nat) (hs : s ≤ ys.length) :
    runLen (ys ++ [c]) s = (bump ys.length c (s, runLen ys s)).2 := by
  have hle : runLen ys s ≤ ys.length - s := by
    have := (List.takeWhile_sublist (fun c => !isWs c) (l := ys.drop s)).length_le
    unfold runLen; simpa using this
  unfold runLen at *
  unfold bump
  rw [List.drop_append_of_le_length hs, List.takeWhile_append]
  simp only [List.length_drop]
  by_cases h : ((ys.drop s).takeWhile (fun c => !isWs c)).length = ys.length - s
  · cases hc : isWs c <;> simp [h, hc, Nat.add_sub_cancel' hs]
  · have h' : ¬ (s + ((ys.drop s).takeWhile (fun c => !isWs c)).length = ys.length) := by omega
    simp [h, h']

theorem startsAt_snoc (ys : List (BitVec 8)) (c : BitVec 8) (s : Nat) (hs : s < ys.length) :
    startsAt (ys ++ [c]) s = startsAt ys s := by
  unfold startsAt
  rw [List.getElem?_append_left hs, List.getElem?_append_left (by omega)]

theorem tokensRef_snoc (ys : List (BitVec 8)) (c : BitVec 8) :
    tokensRef (ys ++ [c]) = (tokensRef ys).map (bump ys.length c) ++
      (if !isWs c && (ys.length == 0 || ys[ys.length - 1]?.any isWs) then [(ys.length, 1)]
       else []) := by
  unfold tokensRef
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
    List.map_append, List.map_map]
  congr 1
  · rw [List.filter_congr (q := startsAt ys) (fun s hs => startsAt_snoc ys c s
      (List.mem_range.mp hs))]
    apply List.map_congr_left
    intro s hs
    have := List.mem_range.mp (List.mem_filter.mp hs).1
    simp only [Function.comp, runLen_snoc ys c s (by omega)]
    unfold bump; split <;> simp_all
  · have h1 : startsAt (ys ++ [c]) ys.length = (!isWs c && (ys.length == 0 || ys[ys.length - 1]?.any isWs)) := by
      unfold startsAt
      by_cases h0 : ys.length = 0
      · simp [h0]
      · have hne : ys ≠ [] := by intro h; simp [h] at h0
        rw [List.getElem?_append_left (l₂ := [c]) (i := ys.length - 1) (by omega)]; simp
    have h2 : runLen (ys ++ [c]) ys.length = if isWs c then 0 else 1 := by
      unfold runLen; cases hc : isWs c <;> simp [hc]
    simp only [List.filter_cons, List.filter_nil, h1]
    split <;> simp_all

@[simp] theorem fill_length (orig : List (BitVec 32)) (vals : List Nat) :
    (fill orig vals).length = orig.length := by
  simp only [fill, List.length_append, List.length_take, List.length_map, List.length_drop]; omega

/-- The bytes so far end inside a token: the last one is not whitespace. -/
def inTok (ys : List (BitVec 8)) : Bool := ys.getLast?.any (fun c => !isWs c)

/-- The tokens already finished: all but an unfinished last one. -/
def done (ys : List (BitVec 8)) : List (Nat × Nat) :=
  if inTok ys then (tokensRef ys).dropLast else tokensRef ys

/-- The start of the last token (0 if there is none). -/
def lastStart (ys : List (BitVec 8)) : Nat := ((tokensRef ys).getLast?.map (·.1)).getD 0

@[simp] theorem inTok_snoc (ys : List (BitVec 8)) (c : BitVec 8) : inTok (ys ++ [c]) = !isWs c := by
  simp [inTok]

theorem startCond_eq (ys : List (BitVec 8)) :
    (ys.length == 0 || ys[ys.length - 1]?.any isWs) = !inTok ys := by
  unfold inTok
  rw [List.getLast?_eq_getElem?]
  by_cases h : ys.length = 0
  · simp [h]
  · rw [List.getElem?_eq_getElem (by omega)]; simp [h]

theorem bump_of_lt {n : Nat} {c : BitVec 8} {t : Nat × Nat} (h : t.1 + t.2 < n) : bump n c t = t := by
  unfold bump; split
  · omega
  · rfl

theorem map_bump {n : Nat} {c : BitVec 8} {D : List (Nat × Nat)} (h : ∀ t ∈ D, t.1 + t.2 < n) :
    D.map (bump n c) = D := by
  conv => rhs; rw [← List.map_id D]
  exact List.map_congr_left fun t ht => bump_of_lt (h t ht)

/-- The shape of the token list of any byte string: finished tokens, all ending before the end,
then possibly one more running up to the end. -/
theorem tokens_shape (ys : List (BitVec 8)) : ∃ D, (∀ t ∈ D, t.1 + t.2 < ys.length) ∧
    ((inTok ys = false ∧ tokensRef ys = D) ∨
     (inTok ys = true ∧ ∃ s, s < ys.length ∧ tokensRef ys = D ++ [(s, ys.length - s)])) := by
  suffices ∀ n (ys : List (BitVec 8)), ys.length = n → ∃ D, (∀ t ∈ D, t.1 + t.2 < ys.length) ∧
    ((inTok ys = false ∧ tokensRef ys = D) ∨
     (inTok ys = true ∧ ∃ s, s < ys.length ∧ tokensRef ys = D ++ [(s, ys.length - s)])) from
    this _ ys rfl
  intro n
  induction n with
  | zero =>
    intro ys h
    obtain rfl := List.eq_nil_of_length_eq_zero h
    exact ⟨[], by simp, Or.inl ⟨rfl, rfl⟩⟩
  | succ n ih =>
    intro ys h
    have hne : ys ≠ [] := by intro e; simp [e] at h
    rw [← List.dropLast_concat_getLast hne]
    generalize ys.getLast hne = c
    have hl : ys.dropLast.length = n := by simp [h]
    generalize ys.dropLast = zs at hl
    obtain ⟨D, hD, hcase⟩ := ih zs hl
    rw [tokensRef_snoc, startCond_eq, inTok_snoc]
    simp only [List.length_append, List.length_singleton]
    cases hc : isWs c
    · -- not whitespace: a token starts, or the current one grows
      rcases hcase with ⟨hin, ht⟩ | ⟨hin, s, hs, ht⟩
      · refine ⟨D, fun t ht' => by have := hD t ht'; omega, Or.inr ⟨rfl, zs.length, by omega, ?_⟩⟩
        simp [hin, ht, map_bump hD]
      · refine ⟨D, fun t ht' => by have := hD t ht'; omega, Or.inr ⟨rfl, s, by omega, ?_⟩⟩
        simp [hin, ht, map_bump hD, bump, hc, Nat.add_sub_cancel' (Nat.le_of_lt hs)]; omega
    · -- whitespace: the current token (if any) is finished
      rcases hcase with ⟨hin, ht⟩ | ⟨hin, s, hs, ht⟩
      · refine ⟨D, fun t ht' => by have := hD t ht'; omega, Or.inl ⟨rfl, ?_⟩⟩
        simp [hin, ht, map_bump hD]
      · refine ⟨D ++ [(s, zs.length - s)], fun t ht' => ?_, Or.inl ⟨rfl, ?_⟩⟩
        · simp only [List.mem_append, List.mem_singleton] at ht'
          rcases ht' with ht' | rfl
          · have := hD t ht'; omega
          · simp only; omega
        · simp [hin, ht, map_bump hD, bump, hc]

/-- The token list is the finished tokens plus, inside a token, the running one. -/
theorem tokensRef_split (ys : List (BitVec 8)) :
    tokensRef ys = done ys ++ (if inTok ys then [(lastStart ys, ys.length - lastStart ys)] else []) := by
  obtain ⟨D, -, ⟨hin, ht⟩ | ⟨hin, s, -, ht⟩⟩ := tokens_shape ys
  · simp [done, hin, ht]
  · simp [done, lastStart, hin, ht]

theorem done_ends (ys : List (BitVec 8)) : ∀ t ∈ done ys, t.1 + t.2 < ys.length := by
  obtain ⟨D, hD, ⟨hin, ht⟩ | ⟨hin, s, -, ht⟩⟩ := tokens_shape ys
  · simpa [done, hin, ht] using hD
  · simpa [done, hin, ht] using hD

theorem lastStart_lt (ys : List (BitVec 8)) (h : inTok ys = true) : lastStart ys < ys.length := by
  obtain ⟨D, hD, ⟨hin, ht⟩ | ⟨hin, s, hs, ht⟩⟩ := tokens_shape ys
  · simp [hin] at h
  · simpa [lastStart, ht] using hs

/-- One more byte, for the finished tokens. -/
@[simp] theorem done_snoc (ys : List (BitVec 8)) (c : BitVec 8) :
    done (ys ++ [c]) = if isWs c = true ∧ inTok ys = true then
      done ys ++ [(lastStart ys, ys.length - lastStart ys)] else done ys := by
  have e := tokensRef_snoc ys c
  rw [startCond_eq] at e
  obtain ⟨D, hD, ⟨hin, ht⟩ | ⟨hin, s, hs, ht⟩⟩ := tokens_shape ys <;> cases hc : isWs c
  · simp [done, hin, ht, hc, e, map_bump hD]
  · simp [done, hin, ht, hc, e, map_bump hD]
  · simp [done, hin, ht, hc, e, map_bump hD, bump, Nat.add_sub_cancel' (Nat.le_of_lt hs)]
  · simp [done, lastStart, hin, ht, hc, e, map_bump hD, bump, Nat.add_sub_cancel' (Nat.le_of_lt hs)]

/-- One more byte, for the start of the last token. -/
@[simp] theorem lastStart_snoc (ys : List (BitVec 8)) (c : BitVec 8) :
    lastStart (ys ++ [c]) = if isWs c = false ∧ inTok ys = false then ys.length else lastStart ys := by
  have e := tokensRef_snoc ys c
  rw [startCond_eq] at e
  obtain ⟨D, hD, ⟨hin, ht⟩ | ⟨hin, s, hs, ht⟩⟩ := tokens_shape ys <;> cases hc : isWs c
  · simp [lastStart, hin, ht, hc, e, map_bump hD]
  · simp [lastStart, hin, ht, hc, e, map_bump hD]
  · simp [lastStart, hin, ht, hc, e, map_bump hD, bump, Nat.add_sub_cancel' (Nat.le_of_lt hs)]
  · simp [lastStart, hin, ht, hc, e, map_bump hD, bump, Nat.add_sub_cancel' (Nat.le_of_lt hs)]

theorem done_length_le (ys : List (BitVec 8)) :
    (done ys).length + (if inTok ys then 1 else 0) ≤ ys.length := by
  have h1 := congrArg List.length (tokensRef_split ys)
  have h2 : (tokensRef ys).length ≤ ys.length := by
    unfold tokensRef
    simpa using List.length_filter_le (startsAt ys) (List.range ys.length)
  cases hin : inTok ys <;> simp [hin] at h1 ⊢ <;> omega

/-! Indexed versions, `f xs i = f (xs.take i)`: the loop's state after `i` bytes. -/

def inTokAt (xs : List (BitVec 8)) (i : Nat) : Bool := inTok (xs.take i)
def doneAt (xs : List (BitVec 8)) (i : Nat) : List (Nat × Nat) := done (xs.take i)
def lastAt (xs : List (BitVec 8)) (i : Nat) : Nat := lastStart (xs.take i)

@[simp] theorem inTokAt_zero (xs : List (BitVec 8)) : inTokAt xs 0 = false := rfl
@[simp] theorem doneAt_zero (xs : List (BitVec 8)) : doneAt xs 0 = [] := rfl
@[simp] theorem lastAt_zero (xs : List (BitVec 8)) : lastAt xs 0 = 0 := rfl

@[simp] theorem inTokAt_succ (xs : List (BitVec 8)) (i : Nat) (h : i < xs.length) :
    inTokAt xs (i + 1) = !isWs xs[i] := by
  simp only [inTokAt, List.take_succ_eq_append_getElem h, inTok_snoc]

@[simp] theorem doneAt_succ (xs : List (BitVec 8)) (i : Nat) (h : i < xs.length) :
    doneAt xs (i + 1) = if isWs xs[i] = true ∧ inTokAt xs i = true then
      doneAt xs i ++ [(lastAt xs i, i - lastAt xs i)] else doneAt xs i := by
  simp only [doneAt, inTokAt, lastAt, List.take_succ_eq_append_getElem h, done_snoc,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  rfl

@[simp] theorem lastAt_succ (xs : List (BitVec 8)) (i : Nat) (h : i < xs.length) :
    lastAt xs (i + 1) = if isWs xs[i] = false ∧ inTokAt xs i = false then i else lastAt xs i := by
  simp only [inTokAt, lastAt, List.take_succ_eq_append_getElem h, lastStart_snoc,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt h)]
  rfl

theorem fill_snoc (orig : List (BitVec 32)) (vals : List Nat) (x : Nat) :
    fill orig (vals ++ [x]) = if vals.length < orig.length then
      (fill orig vals).set vals.length (BitVec.ofNat 32 x) else fill orig vals := by
  apply List.ext_getElem?
  intro j
  unfold fill
  split
  · simp only [List.getElem?_set, List.getElem?_append, List.length_append, List.length_take,
      List.length_map, List.length_drop, List.getElem?_take, List.getElem?_drop, List.length_singleton,
      List.map_append, List.map_cons, List.map_nil]
    grind
  · simp only [List.getElem?_append, List.length_append, List.length_take,
      List.length_map, List.getElem?_take, List.getElem?_drop, List.length_singleton,
      List.map_append, List.map_cons, List.map_nil]
    grind

@[simp] theorem fill_nil (orig : List (BitVec 32)) : fill orig [] = orig := by simp [fill]

/-- At the end of the input, the finished tokens plus the running one are all the tokens. -/
theorem tokensRef_at_end (xs : List (BitVec 8)) : tokensRef xs = doneAt xs xs.length ++
    (if inTokAt xs xs.length then [(lastAt xs xs.length, xs.length - lastAt xs xs.length)] else []) := by
  have := tokensRef_split xs
  simpa [doneAt, inTokAt, lastAt] using this

/-- The code's whitespace test, as `lc_auto` leaves it in a branch, is `isWs`. -/
theorem isWs_fold (c : BitVec 8) :
    (((c = 32#8 ∨ c = 9#8) ∨ c = 10#8) ∨ c = 13#8) ↔ isWs c = true := by
  simp [isWs]

theorem isWs_fold_not (c : BitVec 8) :
    (((¬c = 32#8 ∧ ¬c = 9#8) ∧ ¬c = 10#8) ∧ ¬c = 13#8) ↔ isWs c = false := by
  simp [isWs]

def tokInv (p sp lp : Ptr) (xs : List (BitVec 8)) (S L : List (BitVec 32)) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ lastAt xs i ≤ i ∧
    (doneAt xs i).length + (if inTokAt xs i then 1 else 0) ≤ i ∧
    st.get "p" = some (.ptr .u8 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "starts" = some (.ptr .u32 sp) ∧ st.get "lens" = some (.ptr .u32 lp) ∧
    st.get "cap" = some (nu32 S.length) ∧ st.get "i" = some (nu32 i) ∧
    st.get "cnt" = some (nu32 (doneAt xs i).length) ∧
    st.get "st" = some (nu32 (lastAt xs i)) ∧
    st.get "intok" = some (.bool (inTokAt xs i)) ∧
    (array p (u8s xs) ∗ (array sp (u32s (fill S ((doneAt xs i).map (·.1)))) ∗
      array lp (u32s (fill L ((doneAt xs i).map (·.2)))))) h

/-- **`tokenize` returns the number of tokens `(tokensRef xs).length`, writes the first `cap` token
starts and lengths over `starts` and `lens` (leaving the rest as they were), and leaves the input
alone**, for any input of length < 2³² and any capacity, inside any memory. -/
theorem tokenize_refines (P : Program) (p sp lp : Ptr) (xs : List (BitVec 8))
    (S L : List (BitVec 32)) (hlen : xs.length < 2 ^ 32) (hcap : S.length < 2 ^ 32)
    (hL : L.length = S.length) (h hf : Heap) (m : Mem)
    (hpre : (array p (u8s xs) ∗ (array sp (u32s S) ∗ array lp (u32s L))) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m' h', tokenize.Returns P [.ptr .u8 p, .u32 xs.length, .ptr .u32 sp, .ptr .u32 lp,
        .u32 S.length] m (nu32 (tokensRef xs).length) m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      (array p (u8s xs) ∗ (array sp (u32s (fill S ((tokensRef xs).map (·.1)))) ∗
        array lp (u32s (fill L ((tokensRef xs).map (·.2)))))) h' := by
  have hinit : tokenize.initStore [.ptr .u8 p, .u32 xs.length, .ptr .u32 sp, .ptr .u32 lp,
      .u32 S.length] = some [("p", .ptr .u8 p), ("n", nu32 xs.length), ("starts", .ptr .u32 sp),
        ("lens", .ptr .u32 lp), ("cap", nu32 S.length)] := by
    simp [Fn.initStore, tokenize, Store.empty]; repeat' constructor
  let post : Val → HProp := fun v h' => v = nu32 (tokensRef xs).length ∧
    (array p (u8s xs) ∗ (array sp (u32s (fill S ((tokensRef xs).map (·.1)))) ∗
        array lp (u32s (fill L ((tokensRef xs).map (·.2)))))) h'
  suffices hbody : swp P tokenize.body (fun st h' => ∃ v, tokenize.result.eval st = some v ∧
      v.ty = tokenize.ret ∧ post v h') _ h by
    obtain ⟨v, m', h', hret, d', hm', rfl, hpost⟩ := Fn.returns_of_swp hinit hbody d hm
    exact ⟨m', h', hret, d', hm', hpost⟩
  lc_auto
  lc_while (tokInv p sp lp xs S L) (counterVariant xs.length)
    [tokInv, counterVariant, isWs_fold, isWs_fold_not, fill_snoc, List.map_set, tokensRef_at_end]
end Examples.Tokenize

#print axioms Examples.Tokenize.tokenize_refines
