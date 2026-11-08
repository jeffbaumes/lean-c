import LC
import Examples.M2

/-!
# Milestone 3: array sum and memcpy, verified with separation logic
-/

open LC Examples.M2

namespace Examples.M3

/-- A list of 32-bit (or 8-bit) words, as LC cell values. -/
abbrev u32s (xs : List (BitVec 32)) : List Val := xs.map (Val.int .u32)
abbrev u8s (xs : List (BitVec 8)) : List Val := xs.map (Val.int .u8)

/-! ## 1. Array sum

```c
uint64_t array_sum(uint32_t *p, uint32_t n) {
  uint32_t i = 0; uint32_t x; uint64_t s = 0;
  while (i < n) { x = p[i]; s = s + (uint64_t)x; i = i + 1; }
  return s;
}
```
-/
def arraySum : Fn where
  name   := "array_sum"
  params := [("p", .ptr .u32), ("n", .int .u32)]
  locals := [("i", .int .u32), ("x", .int .u32), ("s", .int .u64)]
  body   := .block [
    "i" ::= .u32 0,
    "s" ::= .u64 0,
    .while (v "i" <. v "n") (.block [
      .load "x" (v "p") (v "i"),
      "s" ::= v "s" + .cast .u64 (v "x"),
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u64
  result := v "s"

#guard arraySum.typeCheck
-- Block 0 holds [10, 20, 30, 40]. Sum the whole array, a prefix, and run off the end.
def mem0 : Mem := [(0, [.u32 10, .u32 20, .u32 30, .u32 40])]
#guard arraySum.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4] mem0 = .ok (.u64 100, mem0)
#guard arraySum.callMem [.ptr .u32 ⟨0, 1⟩, .u32 2] mem0 = .ok (.u64 50, mem0)   -- p+1, n = 2
#guard arraySum.callMem [.ptr .u32 ⟨0, 0⟩, .u32 5] mem0 = .stuck               -- p[4]: out of bounds
#guard arraySum.callMem [.ptr .u32 ⟨7, 0⟩, .u32 1] mem0 = .stuck               -- no such block

/-- Sum of the first `i` words, as a natural number: the specification. -/
def psum (xs : List (BitVec 32)) (i : Nat) : Nat := ((xs.take i).map BitVec.toNat).sum

theorem psum_succ (xs : List (BitVec 32)) (i : Nat) (hi : i < xs.length) :
    psum xs (i + 1) = psum xs i + xs[i].toNat := by
  unfold psum; rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp

/-- Loop invariant. Compare M2: instead of the *whole* store, we state only the
facts we need (`get` lemmas carry them across unrelated assignments). The owned
fragment is unchanged, because the loop only reads. -/
def sumInv (p : Ptr) (xs : List (BitVec 32)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ st.get "p" = some (.ptr .u32 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "i" = some (nu32 i) ∧ st.get "s" = some (nu64 (psum xs i)) ∧ h = h₀

def sumVar (n : Nat) : Store → Heap → Nat := fun st _ =>
  match st.get "i" with
  | some (.int _ bv) => n - bv.toNat
  | _ => 0

/-- **`array_sum(p, n)` returns the sum of the `n` words at `p`, inside any memory.**

`h` is the fragment `p[0..n)` (precondition `array p xs h`), and `hf` is *everything
else* in memory, which the function provably doesn't touch. Memory is unchanged
afterwards. -/
theorem arraySum_correct (p : Ptr) (xs : List (BitVec 32)) (hlen : xs.length < 2 ^ 32)
    (h hf : Heap) (m : Mem) (ha : array p (u32s xs) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) :
    ∃ m', arraySum.Returns [.ptr .u32 p, .u32 xs.length] m (.u64 (psum xs xs.length)) m' ∧
      m'.heap = m.heap := by
  have hinit : arraySum.initStore [.ptr .u32 p, .u32 xs.length] =
      some [("p", .ptr .u32 p), ("n", nu32 xs.length)] := by
    simp [Fn.initStore, arraySum, Store.empty]; constructor <;> rfl
  suffices hbody : swp arraySum.body (fun st h' => ∃ v, arraySum.result.eval st = some v ∧
      v.ty = arraySum.ret ∧ (v = .u64 (psum xs xs.length) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swp
      (post := fun v h' => v = .u64 (psum xs xs.length) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  have hn32 : xs.length % 2 ^ 32 = xs.length := Nat.mod_eq_of_lt hlen
  simp only [arraySum, Stmt.block]
  apply swp_seq; apply swp_assign rfl
  apply swp_seq; apply swp_assign rfl
  refine swp_while (sumInv p xs h) (sumVar xs.length) ?cond ?step ?exit _ _ ⟨0, by omega, ?init⟩
  case init => simp [psum]; constructor <;> rfl
  case cond =>
    rintro st _ ⟨i, hi, hp, hn, hi', hs, rfl⟩
    simp [hi', hn, intBinOp]
  case step =>
    rintro st _ ⟨i, hi, hp, hn, hi', hs, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    -- the cell we read is owned by `array p xs`, so it's in bounds
    have hcell := array_get ha (k := i) (by simpa using hc)
    simp only [List.getElem_map] at hcell
    apply swp_seq; apply swp_load'
    refine ⟨.u32, p.blk, p.off + i, by simp [Expr.evalAddr, hp, hi', nu32, hi32], _, hcell, rfl, ?_⟩
    apply swp_seq; apply swp_assign'
    simp [hs, nu64, intBinOp]
    apply swp_assign'
    simp [hi', hp, hn, nu32, nu64, intBinOp, sumInv, sumVar, Expr.u32, Val.u32, Val.ofInt]
    have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨i + 1, by omega, ?_, ?_⟩, by omega⟩
    · rw [BitVec.ofNat_add_ofNat]
    · rw [psum_succ xs i hc, ← BitVec.ofNat_add_ofNat]; simp
  case exit =>
    rintro st _ ⟨i, hi, hp, hn, hi', hs, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    obtain rfl : i = xs.length := by omega
    simp [hs]; rfl

/-! ## 2. Bounded memcpy

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
def mem1 : Mem := [(0, [.u8 1, .u8 2, .u8 3]), (1, [.u8 0, .u8 0, .u8 0, .u8 9])]
#guard copy.callMem [.ptr .u8 ⟨1, 0⟩, .ptr .u8 ⟨0, 0⟩, .u32 3] mem1 =
  .ok (.unit, [(0, [.u8 1, .u8 2, .u8 3]), (1, [.u8 1, .u8 2, .u8 3, .u8 9])])   -- byte 3 untouched
#guard copy.callMem [.ptr .u8 ⟨1, 0⟩, .ptr .u8 ⟨0, 0⟩, .u32 4] mem1 = .stuck       -- src[3]: out of bounds
-- Overlapping copy (dst = src + 1) runs fine *here*, and the result is the
-- "smear" that real memcpy may or may not produce. The spec below can't even state it,
-- because ∗ forces the two arrays apart. That is the `restrict` contract of C's memcpy.
#eval copy.callMem [.ptr .u8 ⟨0, 1⟩, .ptr .u8 ⟨0, 0⟩, .u32 2] mem1

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
theorem copy_correct (dst src : Ptr) (ss ds : List (BitVec 8)) (hlen : ss.length < 2 ^ 32)
    (hd : ds.length = ss.length) (h hf : Heap) (m : Mem)
    (hpre : (array dst (u8s ds) ∗ array src (u8s ss)) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) :
    ∃ m' h', copy.Returns [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] m .unit m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h' := by
  have hinit : copy.initStore [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] =
      some [("dst", .ptr .u8 dst), ("src", .ptr .u8 src), ("n", nu32 ss.length)] := by
    simp [Fn.initStore, copy, Store.empty]; repeat' constructor
  suffices hbody : swp copy.body (fun st h' => ∃ v, copy.result.eval st = some v ∧
      v.ty = copy.ret ∧ (v = .unit ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h')) _ h by
    obtain ⟨v, m', h', hret, d', hm', rfl, hpost⟩ := Fn.returns_of_swp
      (post := fun v h' => v = .unit ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h')
      hinit hbody d hm
    exact ⟨m', h', hret, d', hm', hpost⟩
  have hn32 : ss.length % 2 ^ 32 = ss.length := Nat.mod_eq_of_lt hlen
  simp only [copy, Stmt.block]
  apply swp_seq; apply swp_assign rfl
  refine swp_while (copyInv dst src ss ds) (sumVar ss.length) ?cond ?step ?exit _ _
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
    simp [hi', hdst, hsrc, hn, nu32, intBinOp, copyInv, sumVar, Expr.u32, Val.u32, Val.ofInt]
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

end Examples.M3
