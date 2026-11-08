-- Solutions to exercises/core/M3_Exercises.lean.  Run: lake env lean exercises/solutions/M3_Exercises.lean
import LC
import Examples.M3
open LC Examples.M2 Examples.M3

/-! ## M3.1 fill -/
def fill : Fn where
  name := "fill"; params := [("p", .ptr .u8), ("n", .int .u32), ("c", .int .u8)]
  locals := [("i", .int .u32)]
  body := .block [
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [.store (v "p") (v "i") (v "c"), "i" ::= v "i" + .u32 1])
  ]
  ret := .unit; result := .lit .unit

#guard fill.typeCheck
#guard fill.callMem [.ptr .u8 ⟨0, 1⟩, .u32 2, .u8 7] [(0, [.u8 0, .u8 0, .u8 0, .u8 0])] =
  .ok (.unit, [(0, [.u8 0, .u8 7, .u8 7, .u8 0])])
#guard fill.callMem [.ptr .u8 ⟨0, 3⟩, .u32 2, .u8 7] [(0, [.u8 0, .u8 0, .u8 0, .u8 0])] = .stuck

/-! ## M3.2
With `dst = src + 1` over one block, `copy_u8` "smears" the first byte forward (see the
`#eval` in Examples/M3.lean: [1,2,3] becomes [1,1,1]). The postcondition "dst holds the old
src bytes" would be false. The precondition `array dst _ ∗ array src _` can't be satisfied
by overlapping ranges, because ∗ demands disjoint cells, so the theorem simply doesn't apply.
This is C's `restrict` on `memcpy`, now as a proof obligation on the caller. -/

/-! ## M3.3 ∗ is associative (one direction) -/
theorem star_assoc {P Q R : HProp} {h : Heap} : ((P ∗ Q) ∗ R) h → (P ∗ (Q ∗ R)) h := by
  rintro ⟨h12, h3, d, rfl, ⟨h1, h2, d12, rfl, hp, hq⟩, hr⟩
  obtain ⟨d13, d23⟩ := Heap.disjoint_union_left.mp d
  exact ⟨h1, h2.union h3, Heap.disjoint_union_right.mpr ⟨d12, d13⟩, Heap.union_assoc _ _ _,
    hp, h2, h3, d23, rfl, hq, hr⟩

/-! ## M3.4 the frame, concretely: copy doesn't touch any cell outside dst/src -/
theorem copy_preserves (dst src : Ptr) (ss ds : List (BitVec 8)) (hlen : ss.length < 2 ^ 32)
    (hd : ds.length = ss.length) (h hf : Heap) (m : Mem)
    (hpre : (array dst (u8s ds) ∗ array src (u8s ss)) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) (a : Addr) (w : Val) (ha : hf a = some w) :
    ∃ m', copy.Returns [.ptr .u8 dst, .ptr .u8 src, .u32 ss.length] m .unit m' ∧
      m'.read a.1 a.2 = some w := by
  obtain ⟨m', h', hret, d', hm', -⟩ := copy_correct dst src ss ds hlen hd h hf m hpre d hm
  refine ⟨m', hret, ?_⟩
  show m'.heap a = some w
  rw [hm']; exact Heap.union_get_right d' ha
