import LC

/-!
# Searching a `uint32_t` array

* `find_first(a, n, x)`: index of the first `x` in `a[0..n)`, or `n`. Uses `break`.
* `lower_bound(a, n, x)`: binary search in a **sorted** array: the number of elements `< x`.
  The midpoint is `lo + (hi - lo) / 2`, because the famous `(lo + hi) / 2` overflows for large
  arrays (Bloch, "Nearly All Binary Searches and Mergesorts are Broken", 2006). Here, in
  `uint32_t`, that overflow would be *defined* wraparound and silently pick the wrong midpoint.
-/

open LC

namespace Examples.Search

/-! ## `find_first`: linear search with `break` -/

def findFirst : Fn where
  name   := "find_first"
  params := [("a", .ptr .u32), ("n", .int .u32), ("x", .int .u32)]
  locals := [("i", .int .u32), ("t", .int .u32)]
  body   := .block [
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "t" (v "a") (v "i"),
      .ite (v "t" ==. v "x") .brk .skip,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u32
  result := v "i"

#guard findFirst.typeCheck
def searchMem : Mem := [(0, [.u32 5, .u32 7, .u32 7, .u32 9])]
#guard findFirst.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4, .u32 7] searchMem = .ok (.u32 1, searchMem)
#guard findFirst.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4, .u32 8] searchMem = .ok (.u32 4, searchMem)

def findInv (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ st.get "a" = some (.ptr .u32 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "x" = some (.int .u32 x) ∧ st.get "i" = some (nu32 i) ∧
    (∀ j < i, xs[j]? ≠ some x) ∧ h = h₀

/-- **`find_first` returns the first index of `x`, or `n` if there is none.** -/
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
  have hn32 : xs.length % 2 ^ 32 = xs.length := Nat.mod_eq_of_lt hlen
  simp only [findFirst, Stmt.block]
  apply swpo_seq_normal; apply swp_assign rfl
  refine swpo_while (findInv p xs x h) (counterVariant xs.length) ?cond ?step ?exit _ _
    ⟨0, by omega, by simp, by simp, by simp, by simp; rfl, by simp, rfl⟩
  case cond =>
    rintro st _ ⟨i, hi, -, hn, -, hi', -⟩
    simp [hi', hn, intBinOp]
  case exit =>
    rintro st _ ⟨i, hi, -, hn, hx, hi', hne, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    obtain rfl : i = xs.length := by omega
    refine ⟨nu32 xs.length, by simp [Fn.finish, hi']; rfl, rfl, xs.length, rfl,
      Nat.le_refl _, hne, fun hk => absurd hk (Nat.lt_irrefl _)⟩
  case step =>
    rintro st _ ⟨i, hi, hp, hn, hx, hi', hne, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    have hcell := array_get ha (k := i) (by simpa using hc)
    simp only [List.getElem_map] at hcell
    apply swpo_seq_normal; apply swp_load'
    refine ⟨.u32, p.blk, p.off + i, by simp [Expr.evalAddr, hp, hi', nu32, hi32], _, hcell, rfl, ?_⟩
    apply swpo_seq
    apply swpo_ite
    by_cases hxi : xs[i] = x
    · -- found it: break, and the loop ends with i as the answer
      left
      refine ⟨by simp [intBinOp, hx, hxi], swpo_brk ?_⟩
      refine ⟨nu32 i, by simp [Fn.finish, hi']; rfl, rfl, i, rfl, hi, hne,
        fun _ => by simp [List.getElem?_eq_getElem hc, hxi]⟩
    · right
      refine ⟨by simp [intBinOp, hx, hxi], swpo_of_swp (swp_skip ?_)⟩
      apply swpo_of_swp; apply swp_assign'
      simp [hi', hp, hn, hx, nu32, intBinOp, findInv, counterVariant, Expr.u32, Val.u32, Val.ofInt]
      have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
      refine ⟨⟨i + 1, by omega, by rw [BitVec.ofNat_add_ofNat], fun j hj => ?_⟩, by omega⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hne j hj
      · simpa [List.getElem?_eq_getElem hc] using hxi

/-! ## `lower_bound`: binary search -/

def lowerBound : Fn where
  name   := "lower_bound"
  params := [("a", .ptr .u32), ("n", .int .u32), ("x", .int .u32)]
  locals := [("lo", .int .u32), ("hi", .int .u32), ("mid", .int .u32), ("t", .int .u32)]
  body   := .block [
    "lo" ::= .u32 0,
    "hi" ::= v "n",
    .while (v "lo" <. v "hi") (.block [
      "mid" ::= v "lo" + (v "hi" - v "lo") / .u32 2,
      .load "t" (v "a") (v "mid"),
      .ite (v "t" <. v "x") ("lo" ::= v "mid" + .u32 1) ("hi" ::= v "mid")
    ])
  ]
  ret    := .int .u32
  result := v "lo"

#guard lowerBound.typeCheck
#guard lowerBound.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4, .u32 7] searchMem = .ok (.u32 1, searchMem)
#guard lowerBound.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4, .u32 8] searchMem = .ok (.u32 3, searchMem)
#guard lowerBound.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4, .u32 100] searchMem = .ok (.u32 4, searchMem)
#guard lowerBound.callMem [.ptr .u32 ⟨0, 0⟩, .u32 0, .u32 7] searchMem = .ok (.u32 0, searchMem)

/-- `xs` is sorted (as unsigned numbers). -/
def Sorted (xs : List (BitVec 32)) : Prop :=
  ∀ (i j : Nat) (a b : BitVec 32), i ≤ j → xs[i]? = some a → xs[j]? = some b → a.toNat ≤ b.toNat

def lbInv (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32) (h₀ : Heap) : SProp := fun st h =>
  ∃ lo hi, lo ≤ hi ∧ hi ≤ xs.length ∧ st.get "a" = some (.ptr .u32 p) ∧
    st.get "x" = some (.int .u32 x) ∧ st.get "lo" = some (nu32 lo) ∧ st.get "hi" = some (nu32 hi) ∧
    (∀ j a, j < lo → xs[j]? = some a → a.toNat < x.toNat) ∧
    (∀ j a, hi ≤ j → xs[j]? = some a → x.toNat ≤ a.toNat) ∧ h = h₀

def lbVar : Store → Heap → Nat := fun st _ =>
  match st.get "lo", st.get "hi" with
  | some (.int _ a), some (.int _ b) => b.toNat - a.toNat
  | _, _ => 0

/-- **`lower_bound` returns the number of elements less than `x`**, for any sorted array of
length < 2³², inside any memory, leaving memory unchanged. -/
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
  simp only [lowerBound, Stmt.block]
  apply swp_seq; apply swp_assign rfl
  apply swp_seq; apply swp_assign (v := nu32 xs.length) (by simp)
  refine swp_while (lbInv p xs x h) lbVar ?cond ?step ?exit _ _
    ⟨0, xs.length, by omega, by omega, by simp, by simp, by simp; rfl, by simp,
      fun _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun j a hj hx => by simp [List.getElem?_eq_none hj] at hx, rfl⟩
  case cond =>
    rintro st _ ⟨lo, hi, -, -, -, -, hlo, hhi, -⟩
    simp [hlo, hhi, intBinOp]
  case exit =>
    rintro st _ ⟨lo, hi, hle, hhi_le, -, -, hlo, hhi, hbelow, habove, rfl⟩ hc
    have : lo % 2 ^ 32 = lo := Nat.mod_eq_of_lt (by omega)
    have : hi % 2 ^ 32 = hi := Nat.mod_eq_of_lt (by omega)
    simp [nu32, intBinOp, BitVec.ult, *] at hc
    obtain rfl : lo = hi := by omega
    refine ⟨nu32 lo, by simp [hlo], rfl, rfl, lo, rfl, hhi_le, hbelow, habove⟩
  case step =>
    rintro st _ ⟨lo, hi, hle, hhi_le, hp, hx, hlo, hhi, hbelow, habove, rfl⟩ hc
    have hlo32 : lo % 2 ^ 32 = lo := Nat.mod_eq_of_lt (by omega)
    have hhi32 : hi % 2 ^ 32 = hi := Nat.mod_eq_of_lt (by omega)
    simp [hlo, hhi, nu32, intBinOp, BitVec.ult, hlo32, hhi32] at hc
    -- mid = lo + (hi - lo) / 2, computed without overflow
    have hmid : lo + (hi - lo) / 2 < hi := by omega
    have hmid32 : (lo + (hi - lo) / 2) % 2 ^ 32 = lo + (hi - lo) / 2 := Nat.mod_eq_of_lt (by omega)
    apply swp_seq; apply swp_assign (v := nu32 (lo + (hi - lo) / 2))
    · simp [hlo, hhi, nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt,
        bv_sub (Nat.le_of_lt hc) (by omega : hi < 2 ^ 32),
        bv_udiv (by omega : hi - lo < 2 ^ 32) (by omega : 2 < 2 ^ 32), BitVec.ofNat_add_ofNat]
    -- t = a[mid]
    have hcell := array_get ha (k := lo + (hi - lo) / 2) (by simp; omega)
    simp only [List.getElem_map] at hcell
    have hmidx : xs[lo + (hi - lo) / 2]? = some xs[lo + (hi - lo) / 2] :=
      List.getElem?_eq_getElem (by omega)
    apply swp_seq; apply swp_load'
    refine ⟨.u32, p.blk, p.off + (lo + (hi - lo) / 2),
      by simp [Expr.evalAddr, hp, nu32, hmid32], _, hcell, rfl, ?_⟩
    apply swp_ite
    by_cases hlt : (xs[lo + (hi - lo) / 2]).toNat < x.toNat
    · -- a[mid] < x: everything up to mid is < x (sortedness), so lo = mid + 1
      left
      refine ⟨by simp [intBinOp, hx, BitVec.ult, hlt], ?_⟩
      apply swp_assign (v := nu32 (lo + (hi - lo) / 2 + 1))
      · simp [nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt, BitVec.ofNat_add_ofNat]
      refine ⟨⟨lo + (hi - lo) / 2 + 1, hi, by omega, hhi_le, by simp [hp], by simp [hx],
        by simp, by simp [hhi], fun j a hj hja => ?_, habove, rfl⟩, ?_⟩
      · exact Nat.lt_of_le_of_lt (hs j _ a _ (by omega) hja hmidx) hlt
      · simp [lbVar, hlo, hhi, Nat.mod_eq_of_lt (by omega : lo + (hi - lo) / 2 + 1 < 2 ^ 32)]
        omega
    · -- x ≤ a[mid]: everything from mid on is ≥ x, so hi = mid
      right
      refine ⟨by simp [intBinOp, hx, BitVec.ult, hlt], ?_⟩
      apply swp_assign (v := nu32 (lo + (hi - lo) / 2)) (by simp)
      refine ⟨⟨lo, lo + (hi - lo) / 2, by omega, by omega, by simp [hp], by simp [hx],
        by simp [hlo], by simp, hbelow, fun j a hj hja => ?_, rfl⟩, ?_⟩
      · exact Nat.le_trans (Nat.not_lt.mp hlt) (hs _ j _ a hj hmidx hja)
      · simp [lbVar, hlo, hhi, hmid32]
        omega

end Examples.Search
