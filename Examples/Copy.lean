import LC

/-!
# `copy_u8`: a bounded memcpy, proved for separate buffers

The `∗` in the precondition is C's `restrict` contract, turned into a proof obligation
for the caller. See docs/separation-logic.md.
-/

open LC

namespace Examples.Copy

/-! ## The program

```c
void copy_u8(uint8_t *dst, uint8_t *src, uint32_t n) {
  uint32_t i = 0; uint8_t t;
  while (i < n) { t = src[i]; dst[i] = t; i = i + 1; }
}
```
-/
def copy : Fn where
  name   := "copy_u8"
  params := [("dst", .ptr .u8), ("src", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("t", .int .u8)]
  body   := .block [
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "t" (v "src") (v "i"),
      .store (v "dst") (v "i") (v "t"),
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .unit
  result := .lit .unit

#guard copy.typeCheck
def copyMem : Mem := [(0, [.u8 1, .u8 2, .u8 3]), (1, [.u8 0, .u8 0, .u8 0, .u8 9])]
#guard copy.callMem [.ptr .u8 ⟨1, 0⟩, .ptr .u8 ⟨0, 0⟩, .u32 3] copyMem =
  .ok (.unit, [(0, [.u8 1, .u8 2, .u8 3]), (1, [.u8 1, .u8 2, .u8 3, .u8 9])])   -- byte 3 untouched
#guard copy.callMem [.ptr .u8 ⟨1, 0⟩, .ptr .u8 ⟨0, 0⟩, .u32 4] copyMem = .stuck       -- src[3]: out of bounds
-- Overlapping copy (dst = src + 1) runs fine *here*, and the result is the
-- "smear" that real memcpy may or may not produce. The spec below can't even state it,
-- because ∗ forces the two arrays apart. That is the `restrict` contract of C's memcpy.
#eval copy.callMem [.ptr .u8 ⟨0, 1⟩, .ptr .u8 ⟨0, 0⟩, .u32 2] copyMem

theorem copy_step {α} (ss ds : List α) (i : Nat) (hs : i < ss.length) (hd : ds.length = ss.length) :
    (ss.take i ++ ds.drop i).set i ss[i] = ss.take (i + 1) ++ ds.drop (i + 1) := by
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_set, List.getElem?_append, List.length_append, List.length_take,
    List.length_drop, List.getElem?_take, List.getElem?_drop]
  by_cases hji : j = i
  · subst hji; grind
  · grind

/-- Invariant: the first `i` bytes of `dst` already hold `src`'s bytes; the rest are untouched. -/
def copyInv (dst src : Ptr) (ss ds : List (BitVec 8)) : SProp := fun st h =>
  ∃ i, i ≤ ss.length ∧ st.get "dst" = some (.ptr .u8 dst) ∧ st.get "src" = some (.ptr .u8 src) ∧
    st.get "n" = some (nu32 ss.length) ∧ st.get "i" = some (nu32 i) ∧
    (array dst (u8s (ss.take i ++ ds.drop i)) ∗ array src (u8s ss)) h

/-- **`copy_u8(dst, src, n)` copies `n` bytes, for any two *separate* buffers, inside any memory.**

Precondition: `dst` owns bytes `ds`, `src` owns bytes `ss` (same length `n`), and the
two are disjoint (`∗`). Postcondition: `dst` holds `ss`, `src` is unchanged, and the
rest of memory (`hf`) is untouched. -/
theorem copy_correct (P : Program) (dst src : Ptr) (ss ds : List (BitVec 8)) (hlen : ss.length < 2 ^ 32)
    (hd : ds.length = ss.length) (h hf : Heap) (m : Mem)
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
  have hn32 : ss.length % 2 ^ 32 = ss.length := Nat.mod_eq_of_lt hlen
  simp only [copy, Stmt.block]
  apply swp_seq; apply swp_assign rfl
  refine swp_while (copyInv dst src ss ds) (counterVariant ss.length) ?cond ?step ?exit _ _
    ⟨0, by omega, ?init⟩
  case init =>
    refine ⟨by simp, by simp, by simp, by simp; rfl, by simpa using hpre⟩
  case cond =>
    rintro st _ ⟨i, hi, hdst, hsrc, hn, hi', -⟩
    simp [hi', hn, intBinOp]
  case step =>
    rintro st h ⟨i, hi, hdst, hsrc, hn, hi', hsep⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    -- read src[i]: owned by the right part of ∗
    have hsrc_cell : h (src.blk, src.off + i) = some (.int .u8 ss[i]) :=
      star_get_right hsep fun h₂ ha => by
        have := array_get ha (k := i) (by simpa using hc); simpa using this
    -- dst[i] exists: owned by the left part of ∗
    have hlen' : i < (u8s (ss.take i ++ ds.drop i)).length := by simp; omega
    have hdst_cell := star_get_left hsep fun h₁ ha => array_get ha hlen'
    apply swp_seq; apply swp_load'
    refine ⟨.u8, src.blk, src.off + i, by simp [Expr.evalAddr, hsrc, hi', nu32, hi32], _,
      hsrc_cell, rfl, ?_⟩
    apply swp_seq; apply swp_store'
    refine ⟨.u8, dst.blk, dst.off + i, by simp [Expr.evalAddr, hdst, hi', nu32, hi32],
      .int .u8 ss[i], by simp, rfl, ⟨_, hdst_cell⟩, ?_⟩
    apply swp_assign'
    simp [hi', hdst, hsrc, hn, nu32, intBinOp, copyInv, counterVariant, Expr.u32, Val.u32, Val.ofInt]
    have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨i + 1, by omega, ?_, ?_⟩, by omega⟩
    · rw [BitVec.ofNat_add_ofNat]
    · -- the new dst contents: one more byte of src
      refine star_update_left hsep fun h₁ ha => ⟨by simp [array_get ha hlen'], ?_⟩
      have := array_update ha hlen' (.int .u8 ss[i])
      have e : (u8s (ss.take i ++ ds.drop i)).set i (.int .u8 ss[i]) =
          u8s (ss.take (i + 1) ++ ds.drop (i + 1)) := by
        rw [← copy_step ss ds i hc hd]; simp only [u8s, List.map_set]
      rw [e] at this
      simpa [u8s] using this
  case exit =>
    rintro st h ⟨i, hi, hdst, hsrc, hn, hi', hsep⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    obtain rfl : i = ss.length := by omega
    refine ⟨.unit, rfl, rfl, rfl, ?_⟩
    simpa [List.take_length, List.drop_eq_nil_of_le (by omega : ds.length ≤ ss.length)] using hsep


end Examples.Copy

#print axioms Examples.Copy.copy_correct
