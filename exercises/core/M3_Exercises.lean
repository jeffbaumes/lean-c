/-
Milestone 3 exercises. Each one takes 15 minutes or less.
Run:  lake env lean exercises/core/M3_Exercises.lean      (after `lake build`)

Read docs/m3-walkthrough.md and Examples/M3.lean first.
Solutions: exercises/solutions/M3_Exercises.lean.
-/
import LC
import Examples.M3
open LC Examples.M2 Examples.M3

/-! ## M3.1 (🔧 10 min): write a program that stores
`fill(p, n, c)` sets `p[0..n)` to the byte `c`. Copy the shape of `copy` in Examples/M3.lean
(one `.store` per iteration). Then test it with `callMem` on a 4-byte block, filling the
middle two bytes (pointer `⟨0, 1⟩`). Also test a call that runs off the end: what do you get? -/
def fill : Fn where
  name := "fill"; params := [("p", .ptr .u8), ("n", .int .u32), ("c", .int .u8)]
  locals := [("i", .int .u32)]
  body := .skip   -- TODO
  ret := .unit; result := .lit .unit

-- #guard fill.typeCheck
-- #guard fill.callMem [.ptr .u8 ⟨0, 1⟩, .u32 2, .u8 7] [(0, [.u8 0, .u8 0, .u8 0, .u8 0])] =
--   .ok (.unit, [(0, [.u8 0, .u8 7, .u8 7, .u8 0])])

/-! ## M3.2 (✍️ 5 min): why `∗` in memcpy's spec?
Look at the overlapping-copy `#eval` in Examples/M3.lean. In two or three sentences:
what would go wrong with `copy_correct` if its precondition used `∧` instead of `∗`?
How does this relate to `restrict` in C's `memcpy` signature? -/

/-! ## M3.3 (🔧 10 min): ∗ is associative
Hint: `rintro ⟨h12, h3, d, rfl, ⟨h1, h2, d12, rfl, hp, hq⟩, hr⟩`, then use
`Heap.disjoint_union_left`, `Heap.disjoint_union_right` and `Heap.union_assoc` from LC/Logic/Sep.lean. -/
theorem star_assoc {P Q R : HProp} {h : Heap} : ((P ∗ Q) ∗ R) h → (P ∗ (Q ∗ R)) h := by
  sorry

/-! ## M3.4 (🔧 10 min): the frame, concretely
`copy_correct` says memory outside `dst`/`src` (the frame `hf`) is untouched. Turn that
into a statement about one cell: if `hf a = some w`, then after the copy `m'.read a.1 a.2 = some w`.
Hint: `obtain` the pieces of `copy_correct`; `m'.read a.1 a.2` is `m'.heap a` by definition
(`show`), and `Heap.union_get_right` finishes it. -/
theorem copy_preserves (dst src : Ptr) (ss ds : List (BitVec 8)) (hlen : ss.length < 2 ^ 32)
    (hd : ds.length = ss.length) (h hf : Heap) (m : Mem)
    (hpre : (array dst (u8s ds) ∗ array src (u8s ss)) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) (a : Addr) (w : Val) (ha : hf a = some w) :
    ∃ m', copy.Returns [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] m .unit m' ∧
      m'.read a.1 a.2 = some w := by
  sorry

/-! ## M3.5 (🔧 stretch, 2 × 15 min): verify `fill`
Prove: from `array p (u8s ds) h` with `ds.length = n`, `fill` ends with
`array p (u8s (List.replicate n c))`. Model it on `copy_correct`: the invariant is
`array p (u8s (List.replicate i c ++ ds.drop i))`, and you need a list lemma like
`copy_step` (try proving it with `List.ext_getElem?` and `grind`). No solution file yet.
Bring me your attempt. -/

/-! ## M3.6 (✍️ 5 min): what the typed-cell memory model can't say
LC's blocks hold *typed* cells (a `u32` block holds `u32`s). Name one real C idiom this
makes impossible to write (hint: think about `memcpy` on a `uint32_t` array, or
`(uint8_t *)&x`). Why is that acceptable for now, and what would M6's bridge to Clight's
*byte* memory have to prove? -/
