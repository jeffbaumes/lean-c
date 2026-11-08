/-
Ring-buffer exercises. Each one takes 15 minutes or less.
Run:  lake env lean exercises/core/RingBuffer.lean      (after `lake build`)
Ring test: nice -n 19 lake exe lc ringtest 200 1

Read docs/ring-buffer.md and Examples/RingBuffer.lean first.
Solutions: exercises/solutions/RingBuffer.lean.
-/
import LC
import Examples.RingBuffer
open LC Examples.RingBuffer

/-! ## Ring.1 (🔧 15 min): tests pass, the proof doesn't
In Examples/RingBuffer.lean, replace `rb_push`'s two-way index computation with the "obvious"
`"idx" ::= (v "head" + v "len") % v "cap"` (drop `room` and the inner `if`). Run the `#guard`s
and `lake exe lc ringtest`. Then look at `rbPush_correct`: which step can no longer be proved,
and what precondition would rescue it? Restore the original afterwards. -/

/-! ## Ring.2 (✍️ 5 min)
`rb` requires `head < cap`, so `cap = 0` never satisfies it. What do `rb_push`/`rb_pop` actually do
when `cap = 0`? Is anything unsafe? Should the spec cover this case? -/

/-! ## Ring.3 (🔧 15 min): compose the specs
Prove that pushing `x` onto an empty buffer and then popping gives back `x`, *using only*
`rbPush_correct` and `rbPop_correct`, not the code. You'll need the frame: when you push,
the `out` byte (`h₂`) is part of the frame; when you pop, it isn't.
Hint: `obtain ⟨h₁, h₂, d₁₂, rfl, hrb, hout⟩ := hpre`, then `Heap.disjoint_union_left/right`
and `Heap.union_assoc` to re-bracket the heaps for each call. -/
theorem push_then_pop (P : Program) (b s o : Ptr) (cap : Nat) (hcap : cap < 2 ^ 32) (hpos : 0 < cap)
    (x : BitVec 8) (w : Val) (h hf : Heap) (m : Mem)
    (hpre : (rb b s cap [] ∗ array o [w]) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m₁ m₂, rbPush.Returns P [.ptr .u8 b, .ptr .u32 s, .u32 cap, .int .u8 x] m (.bool true) m₁ ∧
      rbPop.Returns P [.ptr .u8 b, .ptr .u32 s, .u32 cap, .ptr .u8 o] m₁ (.bool true) m₂ ∧
      m₂.read o.blk o.off = some (.int .u8 x) := by
  sorry

/-! ## Ring.4 (✍️ 10 min): the trusted computing base, concretely
Write down everything you must *trust* to believe "the `rb_push` in generated/lc_examples.c, compiled
with clang, is a correct ring-buffer push". For each item, say whether it is proved, tested,
or only trusted (see the table in docs/ring-buffer.md). -/

/-! ## Ring.5 (🔧 stretch, 2 × 15 min): `rb_len`
Write `rb_len(st) → u32` returning `st[1]`, and prove that from `rb b s cap q h` it returns
`q.length` and leaves the heap unchanged. No solution file yet. -/
