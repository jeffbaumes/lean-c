import LC

/-!
# `array_sum`: reading a buffer, proved with separation logic

See docs/separation-logic.md.
-/

open LC

namespace Examples.ArraySum

/-! ## The program

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
def arraySumMem : Mem := [(0, [.u32 10, .u32 20, .u32 30, .u32 40])]
#guard arraySum.callMem [.ptr .u32 ⟨0, 0⟩, .u32 4] arraySumMem = .ok (.u64 100, arraySumMem)
#guard arraySum.callMem [.ptr .u32 ⟨0, 1⟩, .u32 2] arraySumMem = .ok (.u64 50, arraySumMem)   -- p+1, n = 2
#guard arraySum.callMem [.ptr .u32 ⟨0, 0⟩, .u32 5] arraySumMem = .stuck               -- p[4]: out of bounds
#guard arraySum.callMem [.ptr .u32 ⟨7, 0⟩, .u32 1] arraySumMem = .stuck               -- no such block

/-- Sum of the first `i` words, as a natural number: the specification. -/
def psum (xs : List (BitVec 32)) (i : Nat) : Nat := ((xs.take i).map BitVec.toNat).sum

theorem psum_succ (xs : List (BitVec 32)) (i : Nat) (hi : i < xs.length) :
    psum xs (i + 1) = psum xs i + xs[i].toNat := by
  unfold psum; rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append]; simp

/-- Loop invariant. Compare `sum_to`: instead of the *whole* store, we state only the
facts we need (`get` lemmas carry them across unrelated assignments). The owned
fragment is unchanged, because the loop only reads. -/
def sumInv (p : Ptr) (xs : List (BitVec 32)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ st.get "p" = some (.ptr .u32 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "i" = some (nu32 i) ∧ st.get "s" = some (nu64 (psum xs i)) ∧ h = h₀


/-- **`array_sum(p, n)` returns the sum of the `n` words at `p`, inside any memory.**

`h` is the fragment `p[0..n)` (precondition `array p xs h`), and `hf` is *everything
else* in memory, which the function provably doesn't touch. Memory is unchanged
afterwards. -/
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
  have hn32 : xs.length % 2 ^ 32 = xs.length := Nat.mod_eq_of_lt hlen
  simp only [arraySum, Stmt.block]
  apply swp_seq; apply swp_assign rfl
  apply swp_seq; apply swp_assign rfl
  refine swp_while (sumInv p xs h) (counterVariant xs.length) ?cond ?step ?exit _ _ ⟨0, by omega, ?init⟩
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
    simp [hi', hp, hn, nu32, nu64, intBinOp, sumInv, counterVariant, Expr.u32, Val.u32, Val.ofInt]
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


end Examples.ArraySum
