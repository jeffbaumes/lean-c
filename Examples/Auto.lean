import LC.Auto
import Examples.ArraySum
import Examples.Search
import Examples.Copy
import Examples.ParseU32

/-!
# The example proofs again, with `lc_auto`

Each theorem here restates a spec proved by hand elsewhere in `Examples/` and proves it with
`lc_auto` / `lc_while` / `lc_call`. What's left for the person writing the proof is:

* the boilerplate that turns a body proof into a `Returns` fact (`hinit` and `suffices`);
* the loop invariant and variant;
* the lemmas that are actually about the problem (sortedness, the `copy` list identity, what
  `ParseOk` means).

Compare `Examples/Search.lean` etc. for the hand-written versions of the same proofs.
-/

open LC

namespace Examples.Auto

/-! ## `array_sum` -/

open Examples.ArraySum in
theorem arraySum_correct (P : Program) (p : Ptr) (xs : List (BitVec 32)) (hlen : xs.length < 2 ^ 32)
    (h hf : Heap) (m : Mem) (ha : array p (u32s xs) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) :
    ∃ m', arraySum.Returns P [.ptr .u32 p, .u32 xs.length] m (.u64 (psum xs xs.length)) m' ∧
      m'.heap = m.heap := by
  have hinit : arraySum.initStore [.ptr .u32 p, .u32 xs.length] =
      some [("p", .ptr .u32 p), ("n", nu32 xs.length)] := by
    simp [Fn.initStore, arraySum, Store.empty]; constructor <;> rfl
  suffices hbody : swp P arraySum.body (fun st h' => ∃ v, arraySum.result.eval st = some v ∧
      v.ty = arraySum.ret ∧ (v = .u64 (psum xs xs.length) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swp
      (post := fun v h' => v = .u64 (psum xs xs.length) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (sumInv p xs h) (counterVariant xs.length) [sumInv, counterVariant, psum_succ]

/-! ## `find_first` -/

open Examples.Search in
theorem findFirst_correct (P : Program) (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32)
    (hlen : xs.length < 2 ^ 32) (h hf : Heap) (m : Mem) (ha : array p (u32s xs) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ k m', findFirst.Returns P [.ptr .u32 p, .u32 xs.length, .int .u32 x] m (nu32 k) m' ∧
      m'.heap = m.heap ∧ k ≤ xs.length ∧ (∀ j < k, xs[j]? ≠ some x) ∧
      (k < xs.length → xs[k]? = some x) := by
  have hinit : findFirst.initStore [.ptr .u32 p, .u32 xs.length, .int .u32 x] =
      some [("a", .ptr .u32 p), ("n", nu32 xs.length), ("x", .int .u32 x)] := by
    simp [Fn.initStore, findFirst, Store.empty]; repeat' constructor
  let post : Val → HProp := fun v h' => h' = h ∧ ∃ k, v = nu32 k ∧ k ≤ xs.length ∧
    (∀ j < k, xs[j]? ≠ some x) ∧ (k < xs.length → xs[k]? = some x)
  suffices hbody : swpo P findFirst.body
      (fun o st h' => ∃ v, findFirst.finish o st = some v ∧ post v h') _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, k, rfl, hk⟩ := Fn.returns_of_swpo hinit hbody d hm
    exact ⟨k, m', hret, by rw [hm', hm], hk⟩
  lc_auto
  lc_while (findInv p xs x h) (counterVariant xs.length) [findInv, counterVariant]

/-! ## `lower_bound`

`lc_auto` does everything except the two places sortedness is used. -/

open Examples.Search

theorem sorted_below {xs : List (BitVec 32)} (hs : Sorted xs) {k : Nat} {x : BitVec 32}
    (hk : k < xs.length) (hlt : xs[k].toNat < x.toNat) :
    ∀ j a, j < k + 1 → xs[j]? = some a → a.toNat < x.toNat :=
  fun j a hj hja => Nat.lt_of_le_of_lt (hs j k a _ (by omega) hja (List.getElem?_eq_getElem hk)) hlt

theorem sorted_above {xs : List (BitVec 32)} (hs : Sorted xs) {k : Nat} {x : BitVec 32}
    (hk : k < xs.length) (hge : x.toNat ≤ xs[k].toNat) :
    ∀ j a, k ≤ j → xs[j]? = some a → x.toNat ≤ a.toNat :=
  fun j a hj hja => Nat.le_trans hge (hs k j _ a hj (List.getElem?_eq_getElem hk) hja)

theorem lowerBound_correct (P : Program) (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32)
    (hlen : xs.length < 2 ^ 32) (hs : Sorted xs) (h hf : Heap) (m : Mem)
    (ha : array p (u32s xs) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ k m', lowerBound.Returns P [.ptr .u32 p, .u32 xs.length, .int .u32 x] m (nu32 k) m' ∧
      m'.heap = m.heap ∧ k ≤ xs.length ∧
      (∀ j a, j < k → xs[j]? = some a → a.toNat < x.toNat) ∧
      (∀ j a, k ≤ j → xs[j]? = some a → x.toNat ≤ a.toNat) := by
  have hinit : lowerBound.initStore [.ptr .u32 p, .u32 xs.length, .int .u32 x] =
      some [("a", .ptr .u32 p), ("n", nu32 xs.length), ("x", .int .u32 x)] := by
    simp [Fn.initStore, lowerBound, Store.empty]; repeat' constructor
  let post : Val → HProp := fun v h' => h' = h ∧ ∃ k, v = nu32 k ∧ k ≤ xs.length ∧
    (∀ j a, j < k → xs[j]? = some a → a.toNat < x.toNat) ∧
    (∀ j a, k ≤ j → xs[j]? = some a → x.toNat ≤ a.toNat)
  suffices hbody : swp P lowerBound.body (fun st h' => ∃ v, lowerBound.result.eval st = some v ∧
      v.ty = lowerBound.ret ∧ post v h') _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, k, rfl, hk⟩ := Fn.returns_of_swp hinit hbody d hm
    exact ⟨k, m', hret, by rw [hm', hm], hk⟩
  lc_auto
  lc_while (lbInv p xs x h) lbVar [lbInv, lbVar]
  · exact sorted_below hs (by omega) ‹_›
  · exact sorted_above hs (by omega) ‹_›

/-! ## `copy_u8`

`lc_auto` finds `src[i]` and `dst[i]` inside `array dst _ ∗ array src _`, rewrites the
`dst` array after the store, and leaves just the list identity. -/

theorem copy_step' {α} (ss ds : List α) (i : Nat) (hs : i < ss.length) (hd : ds.length = ss.length) :
    ss.take i ++ (ds.drop i).set 0 ss[i] = ss.take (i + 1) ++ ds.drop (i + 1) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.getElem?_append, List.length_take,
    List.length_drop, List.getElem?_take, List.getElem?_drop]
  grind

open Examples.Copy in
theorem copy_correct (P : Program) (dst src : Ptr) (ss ds : List (BitVec 8))
    (hlen : ss.length < 2 ^ 32) (hd : ds.length = ss.length) (h hf : Heap) (m : Mem)
    (hpre : (array dst (u8s ds) ∗ array src (u8s ss)) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) :
    ∃ m' h', copy.Returns P [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] m .unit m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h' := by
  have hinit : copy.initStore [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] =
      some [("dst", .ptr .u8 dst), ("src", .ptr .u8 src), ("n", nu32 ss.length)] := by
    simp [Fn.initStore, copy, Store.empty]; repeat' constructor
  suffices hbody : swp P copy.body (fun st h' => ∃ v, copy.result.eval st = some v ∧
      v.ty = copy.ret ∧ (v = .unit ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h')) _ h by
    obtain ⟨v, m', h', hret, d', hm', rfl, hpost⟩ := Fn.returns_of_swp
      (post := fun v h' => v = .unit ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h')
      hinit hbody d hm
    exact ⟨m', h', hret, d', hm', hpost⟩
  lc_auto
  lc_while (copyInv dst src ss ds) (counterVariant ss.length) [copyInv, counterVariant]
  · have e := copy_step' (ss.map (Val.int .u8)) (ds.map (Val.int .u8)) _ (by simp; omega)
      (by simp [hd])
    rwa [List.getElem_map] at e


/-! ## `parse_u32`

The call to `is_digit` goes through its spec (`lc_call`). What's left is what `ParseOk`
means at each exit: these four lemmas are the whole of the problem-specific reasoning. -/

namespace ParseU32
open Examples.ParseU32

theorem not_ok_nil : ¬ ParseOk [] := fun ⟨hne, _⟩ => hne rfl

theorem not_ok_of_nondigit {cs : List (BitVec 8)} {i : Nat} (hi : i < cs.length)
    (hd : cs[i].toNat < 48 ∨ 57 < cs[i].toNat) : ¬ ParseOk cs := by
  rintro ⟨_, hall, _⟩
  have := hall _ (List.getElem_mem hi)
  simp only [IsDigit] at this; omega

theorem not_ok_of_overflow {cs : List (BitVec 8)} {i : Nat} (hi : i < cs.length)
    (h48 : 48 ≤ cs[i].toNat) (h57 : cs[i].toNat ≤ 57)
    (hov : (4294967295 - (cs[i].toNat - 48)) / 10 < decVal (cs.take i)) : ¬ ParseOk cs := by
  rintro ⟨_, _, hfit⟩
  have := decVal_take_succ cs i hi
  have := decVal_take_le cs (i + 1)
  omega

theorem digits_succ {cs : List (BitVec 8)} {i : Nat} (hi : i < cs.length)
    (hall : ∀ j c, j < i → cs[j]? = some c → IsDigit c)
    (h48 : 48 ≤ cs[i].toNat) (h57 : cs[i].toNat ≤ 57) :
    ∀ j c, j < i + 1 → cs[j]? = some c → 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro j c hj hjc
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact hall j c hj hjc
  · rw [List.getElem?_eq_getElem hi] at hjc; cases hjc; exact ⟨h48, h57⟩

theorem ok_of_loop {cs : List (BitVec 8)} (h0 : cs ≠ [])
    (hfit : decVal (cs.take cs.length) < 2 ^ 32)
    (hall : ∀ j c, j < cs.length → cs[j]? = some c → IsDigit c) : ParseOk cs := by
  refine ⟨h0, fun c hc => ?_, by simpa using hfit⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  exact hall j _ hj (List.getElem?_eq_getElem hj)

theorem parseU32_correct (P : Program) (hP : P.find? "is_digit" = some isDigit)
    (p o : Ptr) (cs : List (BitVec 8)) (w : Val) (hlen : cs.length < 2 ^ 32)
    (h hf : Heap) (m : Mem) (hpre : (array p (u8s cs) ∗ array o [w]) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', parseU32.Returns P [.ptr .u8 p, .u32 cs.length, .ptr .u32 o] m v m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      ((ParseOk cs ∧ v = .bool true ∧ (array p (u8s cs) ∗ array o [nu32 (decVal cs)]) h') ∨
       (¬ ParseOk cs ∧ v = .bool false ∧ h' = h)) := by
  have hinit : parseU32.initStore [.ptr .u8 p, .u32 cs.length, .ptr .u32 o] =
      some [("p", .ptr .u8 p), ("n", nu32 cs.length), ("out", .ptr .u32 o)] := by
    simp [Fn.initStore, parseU32, Store.empty]; repeat' constructor
  refine Fn.returns_of_swpo hinit ?_ d hm
  lc_auto
  lc_while (parseInv p o cs h) (counterVariant cs.length)
    [parseInv, counterVariant, decVal_take_succ, IsDigit]
  lc_call hP (isDigit_spec P _) (isDigit_init _)
    [parseInv, counterVariant, decVal_take_succ, IsDigit]
  · exact not_ok_of_nondigit ‹_› ‹_›
  · exact not_ok_of_overflow ‹_› ‹_› ‹_› ‹_›
  · exact digits_succ ‹_› ‹_› ‹_› ‹_›
  · exact ok_of_loop ‹_› ‹_› ‹_›
  · simp [decVal]
  · subst_vars; exact not_ok_nil

end ParseU32

/-! ## Short-circuit conditions

`&&.` and `||.` in an `if` or `while` condition are evaluated like any other expression. -/

example (P : Program) (st : Store) (h : Heap) (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (hsa : st.get "a" = some (nu32 a)) (hsb : st.get "b" = some (nu32 b)) :
    swp P (.ite (v "a" ==. .u32 0 ||. v "b" ==. .u32 0) ("r" ::= .u32 0) ("r" ::= .u32 1))
      (fun st _ => ∃ r, st.get "r" = some (nu32 r) ∧ (r = 0 ↔ (a = 0 ∨ b = 0))) st h := by
  lc_auto

def minInv (n m : Nat) : SProp := fun st _ =>
  ∃ i, i ≤ n ∧ i ≤ m ∧ st.get "n" = some (nu32 n) ∧ st.get "m" = some (nu32 m) ∧
    st.get "i" = some (nu32 i)

/-- `while (i < n && i < m) i++` stops at `min n m`. -/
example (P : Program) (st : Store) (h : Heap) (n m : Nat) (hn : n < 2 ^ 32) (hm : m < 2 ^ 32)
    (hsn : st.get "n" = some (nu32 n)) (hsm : st.get "m" = some (nu32 m)) :
    swp P (.block ["i" ::= .u32 0,
        .while (v "i" <. v "n" &&. v "i" <. v "m") ("i" ::= v "i" + .u32 1)])
      (fun st _ => ∃ i, st.get "i" = some (nu32 i) ∧ i = min n m) st h := by
  lc_auto
  lc_while (minInv n m) (counterVariant n) [minInv, counterVariant]

end Examples.Auto

-- No `sorry` and no `native_decide` anywhere in these proofs.
#print axioms Examples.Auto.arraySum_correct
#print axioms Examples.Auto.findFirst_correct
#print axioms Examples.Auto.lowerBound_correct
#print axioms Examples.Auto.copy_correct
#print axioms Examples.Auto.ParseU32.parseU32_correct
