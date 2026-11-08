-- Solutions to exercises/core/RingBuffer.lean.  Run: lake env lean exercises/solutions/RingBuffer.lean
import LC
import Examples.RingBuffer
open LC Examples.RingBuffer

/-! ## Ring.1
With `idx = (head + len) % cap` the interpreter `#guard`s and `lake exe lc ringtest` should still pass (try it):
capacities 1–6 never get near 2³². But for `cap > 2³¹`, `head + len` can exceed 2³² and wrap
(*defined* behaviour, so no sanitizer fires), and `% cap` then picks the wrong slot. The proof
breaks exactly there: the `idx` value is `(head + len) mod 2³² mod cap`, not `slot cap head len`.
You can only finish it by adding `cap ≤ 2³¹` to the precondition. Testing passed; proof refused. -/

/-! ## Ring.2
`rb` requires `head < cap`, so no state with `cap = 0` satisfies it, and the theorems say nothing.
The C is still safe: `rb_push` sees `len < 0` false and returns false; `rb_pop` sees `len = 0`
and returns false; neither touches `buf`. The spec could be extended (`head = 0` when `cap = 0`),
but a zero-capacity queue is useless, so excluding it is a reasonable spec choice. Just make it
a documented one. -/

/-! ## Ring.3 composing the specs: push x, then pop, gives back x -/
theorem push_then_pop (P : Program) (b s o : Ptr) (cap : Nat) (hcap : cap < 2 ^ 32) (hpos : 0 < cap)
    (x : BitVec 8) (w : Val) (h hf : Heap) (m : Mem)
    (hpre : (rb b s cap [] ∗ array o [w]) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m₁ m₂, rbPush.Returns P [.ptr .u8 b, .ptr .u32 s, .u32 cap, .int .u8 x] m (.bool true) m₁ ∧
      rbPop.Returns P [.ptr .u8 b, .ptr .u32 s, .u32 cap, .ptr .u8 o] m₁ (.bool true) m₂ ∧
      m₂.read o.blk o.off = some (.int .u8 x) := by
  obtain ⟨h₁, h₂, d₁₂, rfl, hrb, hout⟩ := hpre
  obtain ⟨d₁f, d₂f⟩ := Heap.disjoint_union_left.mp d
  -- push on h₁, with h₂ (the out byte) joining the frame
  obtain ⟨v₁, m₁, h₁', hret₁, d₁', hm₁, hpost₁⟩ :=
    rbPush_correct P b s cap hcap [] x h₁ (h₂.union hf) m hrb
      (Heap.disjoint_union_right.mpr ⟨d₁₂, d₁f⟩) (by rw [hm, Heap.union_assoc])
  simp only [List.length_nil, hpos, ite_true, List.nil_append] at hpost₁
  obtain ⟨rfl, hrb'⟩ := hpost₁
  obtain ⟨d₁'₂, d₁'f⟩ := Heap.disjoint_union_right.mp d₁'
  -- pop on h₁' ⊎ h₂
  obtain ⟨v₂, m₂, h₂', hret₂, -, hm₂, hpost₂⟩ :=
    rbPop_correct P b s o cap hcap [x] w (h₁'.union h₂) hf m₁ ⟨h₁', h₂, d₁'₂, rfl, hrb', hout⟩
      (Heap.disjoint_union_left.mpr ⟨d₁'f, d₂f⟩) (by rw [hm₁, Heap.union_assoc])
  obtain ⟨rfl, hfin⟩ := hpost₂
  refine ⟨m₁, m₂, hret₁, hret₂, ?_⟩
  show m₂.heap (o.blk, o.off) = _
  rw [hm₂]
  exact Heap.union_get_left (by simpa using star_get_right hfin fun _ ha => array_get ha (k := 0) (by simp))
