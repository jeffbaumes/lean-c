import LC
import Examples.M3

/-!
# Milestone 5: a ring buffer, verified end to end

A fixed-capacity FIFO queue of bytes over caller-provided storage:

```c
// buf: cap bytes of storage.   st: st[0] = head index, st[1] = current length.
bool rb_push(uint8_t *buf, uint32_t *st, uint32_t cap, uint8_t x);   // false if full
bool rb_pop (uint8_t *buf, uint32_t *st, uint32_t cap, uint8_t *out); // false if empty
```

LC has no structs yet, so the header `{head, len}` lives in a two-word array `st`,
and `cap` is passed in.

**No `%` and no overflow.** The obvious index `(head + len) % cap` can overflow `uint32_t`
when `cap > 2³¹`, and then silently picks the wrong slot. That's *defined* wraparound, so
UB-checking wouldn't notice. Instead we compute the slot by comparing against `cap - head`,
which can't overflow because `head < cap`. The proof below would fail for the `%` version
unless its precondition required `cap ≤ 2³¹`.
-/

open LC Examples.M2 Examples.M3

namespace Examples.M5

def rbPush : Fn where
  name   := "rb_push"
  params := [("buf", .ptr .u8), ("st", .ptr .u32), ("cap", .int .u32), ("x", .int .u8)]
  locals := [("head", .int .u32), ("len", .int .u32), ("room", .int .u32),
             ("idx", .int .u32), ("ok", .bool)]
  body   := .block [
    .load "head" (v "st") (.u32 0),
    .load "len" (v "st") (.u32 1),
    .ite (v "len" <. v "cap")
      (.block [
        "room" ::= v "cap" - v "head",
        .ite (v "len" <. v "room") ("idx" ::= v "head" + v "len") ("idx" ::= v "len" - v "room"),
        .store (v "buf") (v "idx") (v "x"),
        .store (v "st") (.u32 1) (v "len" + .u32 1),
        "ok" ::= .tt
      ])
      ("ok" ::= .ff)
  ]
  ret    := .bool
  result := v "ok"

def rbPop : Fn where
  name   := "rb_pop"
  params := [("buf", .ptr .u8), ("st", .ptr .u32), ("cap", .int .u32), ("out", .ptr .u8)]
  locals := [("head", .int .u32), ("len", .int .u32), ("c", .int .u8), ("ok", .bool)]
  body   := .block [
    .load "head" (v "st") (.u32 0),
    .load "len" (v "st") (.u32 1),
    .ite (.u32 0 <. v "len")
      (.block [
        .load "c" (v "buf") (v "head"),
        .store (v "out") (.u32 0) (v "c"),
        "head" ::= v "head" + .u32 1,
        .ite (v "head" ==. v "cap") ("head" ::= .u32 0) .skip,
        .store (v "st") (.u32 0) (v "head"),
        .store (v "st") (.u32 1) (v "len" - .u32 1),
        "ok" ::= .tt
      ])
      ("ok" ::= .ff)
  ]
  ret    := .bool
  result := v "ok"

#guard rbPush.typeCheck && rbPop.typeCheck
#guard (cTranslationUnit [rbPush, rbPop]).isOk
#guard !(cTranslationUnit [rbPush, rbPush]).isOk   -- duplicate names are refused

/-! ## Quick interpreter checks

Block 0 is `buf` (capacity 3), block 1 is `st`, block 2 is `out`. -/

def bufP : Ptr := ⟨0, 0⟩
def stP : Ptr := ⟨1, 0⟩
def outP : Ptr := ⟨2, 0⟩

def push (m : Mem) (x : Nat) : Result (Val × Mem) :=
  rbPush.callMem [.ptr .u8 bufP, .ptr .u32 stP, .u32 3, .u8 x] m
def pop (m : Mem) : Result (Val × Mem) :=
  rbPop.callMem [.ptr .u8 bufP, .ptr .u32 stP, .u32 3, .ptr .u8 outP] m

def empty3 : Mem := [(0, [.u8 0, .u8 0, .u8 0]), (1, [.u32 0, .u32 0]), (2, [.u8 0])]

/-- Run a script of operations (`some x` = push x, `none` = pop) and collect what each
returns: push → `ok?`; pop → the popped byte, or `none` when empty. -/
def script (m : Mem) : List (Option Nat) → List String
  | [] => []
  | some x :: ops =>
    match push m x with
    | .ok (.bool b, m') => s!"push {x}: {b}" :: script m' ops
    | _ => ["push: stuck"]
  | none :: ops =>
    match pop m with
    | .ok (.bool true, m') =>
      match m'.read 2 0 with
      | some w => s!"pop: {w}" :: script m' ops
      | none => ["pop: no out"]
    | .ok (.bool false, m') => "pop: empty" :: script m' ops
    | _ => ["pop: stuck"]

-- fill past capacity, drain past empty, and wrap the head around the end
#guard script empty3 [some 1, some 2, some 3, some 4, none, some 5, none, none, none, none] =
  ["push 1: true", "push 2: true", "push 3: true", "push 4: false",
   "pop: 1u8", "push 5: true", "pop: 2u8", "pop: 3u8", "pop: 5u8", "pop: empty"]

/-! ## The specification

The abstract model is a list `q` of bytes, front first. `slot cap head k` is where
logical element `k` lives: `head + k`, wrapping once past the end. -/

def slot (cap head k : Nat) : Nat := if head + k < cap then head + k else head + k - cap

/-- **Representation invariant.** `buf` (`cap` cells) and `st` (`[head, len]`) represent the
queue `q`: `head` is in range, `len = q.length ≤ cap`, and logical element `k` sits at
`buf[slot cap head k]`. Cells outside the queue hold anything. -/
def rb (b s : Ptr) (cap : Nat) (q : List (BitVec 8)) : HProp := fun h =>
  ∃ (cells : List Val) (head : Nat), cells.length = cap ∧ head < cap ∧ q.length ≤ cap ∧
    (∀ k (hk : k < q.length), cells[slot cap head k]? = some (.int .u8 q[k])) ∧
    (array b cells ∗ array s [nu32 head, nu32 q.length]) h

theorem slot_lt {cap head k : Nat} (hh : head < cap) (hk : k < cap) : slot cap head k < cap := by
  unfold slot; split <;> omega

theorem slot_inj {cap head j k : Nat} (hj : j < cap) (hk : k < cap)
    (e : slot cap head j = slot cap head k) : j = k := by
  unfold slot at e; split at e <;> split at e <;> omega

theorem bv_sub {w a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ w) :
    BitVec.ofNat w a - BitVec.ofNat w b = BitVec.ofNat w (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ w), Nat.mod_eq_of_lt ha]
  have : 2 ^ w - b + a = (a - b) + 2 ^ w := by omega
  rw [this, Nat.add_mod_right]

/-! ## `rb_push` is correct -/

theorem rbPush_correct (b s : Ptr) (cap : Nat) (hcap : cap < 2 ^ 32) (q : List (BitVec 8))
    (x : BitVec 8) (h hf : Heap) (m : Mem)
    (hrb : rb b s cap q h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', rbPush.Returns [.ptr .u8 b, .ptr .u32 s, .u32 cap, .int .u8 x] m v m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      (if q.length < cap then v = .bool true ∧ rb b s cap (q ++ [x]) h'
       else v = .bool false ∧ rb b s cap q h') := by
  obtain ⟨cells, head, hlen, hhead, hq, hcells, hsep⟩ := hrb
  have hinit : rbPush.initStore [.ptr .u8 b, .ptr .u32 s, .u32 cap, .int .u8 x] =
      some [("buf", .ptr .u8 b), ("st", .ptr .u32 s), ("cap", nu32 cap), ("x", .int .u8 x)] := by
    simp [Fn.initStore, rbPush, Store.empty]; repeat' constructor
  refine Fn.returns_of_swp hinit ?_ d hm
  -- the two header cells
  have hh0 : h (s.blk, s.off) = some (nu32 head) := by
    simpa using star_get_right hsep (fun _ ha => array_get ha (k := 0) (by simp))
  have hh1 : h (s.blk, s.off + 1) = some (nu32 q.length) := by
    simpa using star_get_right hsep (fun _ ha => array_get ha (k := 1) (by simp))
  have hc32 : cap % 2 ^ 32 = cap := Nat.mod_eq_of_lt hcap
  have hh32 : head % 2 ^ 32 = head := Nat.mod_eq_of_lt (by omega)
  have hl32 : q.length % 2 ^ 32 = q.length := Nat.mod_eq_of_lt (by omega)
  simp only [rbPush, Stmt.block]
  apply swp_seq; apply swp_load'
  refine ⟨.u32, s.blk, s.off, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt], _, hh0, rfl, ?_⟩
  apply swp_seq; apply swp_load'
  refine ⟨.u32, s.blk, s.off + 1, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt], _, hh1, rfl, ?_⟩
  apply swp_ite
  by_cases hlt : q.length < cap
  · left
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, hc32, hl32, hlt], ?_⟩
    -- room = cap - head (no wrap: head < cap)
    apply swp_seq; apply swp_assign'
    refine ⟨nu32 (cap - head), by simp [nu32, intBinOp, bv_sub (Nat.le_of_lt hhead) hcap], ?_⟩
    have hr32 : (cap - head) % 2 ^ 32 = cap - head := Nat.mod_eq_of_lt (by omega)
    -- idx = slot cap head len, computed two ways
    apply swp_seq; apply swp_ite
    rcases Nat.lt_or_ge q.length (cap - head) with hsplit | hsplit
    -- (no bullets: each branch leaves the *same* tail goal, proved once with `all_goals`)
    left
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, hl32, hr32, hsplit], ?_⟩
    apply swp_assign'
    refine ⟨nu32 (slot cap head q.length),
      by simp [nu32, intBinOp, BitVec.ofNat_add_ofNat, slot, show head + q.length < cap by omega], ?_⟩
    rotate_left
    right
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, hl32, hr32, Nat.not_lt.mpr hsplit], ?_⟩
    apply swp_assign'
    refine ⟨nu32 (slot cap head q.length), ?_, ?_⟩
    · simp [nu32, intBinOp, bv_sub hsplit (by omega : q.length < 2 ^ 32), slot,
        show ¬(head + q.length < cap) by omega]
      congr 1; omega
    -- common tail: write buf[idx] := x, then st[1] := len + 1, then ok := true
    all_goals
      have hsl : slot cap head q.length < cells.length := by rw [hlen]; exact slot_lt hhead hlt
      have hbcell := star_get_left hsep fun _ ha => array_get ha hsl
      have hsep1 := star_update_left (v := .int .u8 x) hsep fun _ ha =>
        ⟨by simp [array_get ha hsl], array_update ha hsl _⟩
      apply swp_seq; apply swp_store'
      refine ⟨.u8, b.blk, b.off + slot cap head q.length,
        by simp [Expr.evalAddr, nu32, Nat.mod_eq_of_lt (show slot cap head q.length < 2 ^ 32 by omega)],
        .int .u8 x, by simp, rfl, ⟨_, hbcell⟩, ?_⟩
      have hscell : (h.update (b.blk, b.off + slot cap head q.length) (.int .u8 x))
          (s.blk, s.off + 1) = some (nu32 q.length) := by
        simpa using star_get_right hsep1 (fun _ ha => array_get ha (k := 1) (by simp))
      have hsep2 := star_update_right (v := nu32 (q.length + 1)) hsep1 fun _ ha =>
        ⟨by simp [array_get ha (k := 1) (by simp)], array_update ha (k := 1) (by simp) _⟩
      apply swp_seq; apply swp_store'
      refine ⟨.u32, s.blk, s.off + 1, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt],
        nu32 (q.length + 1), by simp [nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt,
          BitVec.ofNat_add_ofNat], rfl, ⟨_, hscell⟩, ?_⟩
      apply swp_assign'
      refine ⟨_, rfl, ?_⟩
      simp only [Store.get_set_same, Expr.eval_v, hlt, ite_true]
      refine ⟨_, rfl, rfl, rfl, cells.set (slot cap head q.length) (.int .u8 x), head,
        by simp [hlen], hhead, by simp; omega, ?_, by simpa using hsep2⟩
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hkq : k < q.length
      · rw [List.getElem?_set_ne (fun e => by
            have := slot_inj (cap := cap) (head := head) (by omega) (by omega) e; omega),
          hcells k hkq, List.getElem_append_left hkq]
      · obtain rfl : k = q.length := by omega
        simp [List.getElem?_set_self hsl]
  · right
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, hc32, hl32, hlt], ?_⟩
    apply swp_assign'
    simp [hlt]
    exact ⟨rfl, cells, head, hlen, hhead, hq, hcells, hsep⟩


/-! ## `rb_pop` is correct -/

/-- What `rb_pop` promises: on an empty queue it returns `false` and changes nothing; otherwise
it returns `true`, writes the front byte to `out[0]`, and the queue loses its front. -/
def popPost (b s o : Ptr) (cap : Nat) (q : List (BitVec 8)) (w : Val) : Val → HProp :=
  fun v h' => match q with
    | [] => v = .bool false ∧ (rb b s cap [] ∗ array o [w]) h'
    | a :: q' => v = .bool true ∧ (rb b s cap q' ∗ array o [.int .u8 a]) h'

theorem slot_one_lt {cap head : Nat} (hh : head < cap) : slot cap head 1 < cap := by
  unfold slot; split <;> omega

theorem slot_succ {cap head k : Nat} (hh : head < cap) (hk : k + 1 < cap) :
    slot cap (slot cap head 1) k = slot cap head (k + 1) := by
  unfold slot; split <;> split <;> split <;> omega

theorem rbPop_correct (b s o : Ptr) (cap : Nat) (hcap : cap < 2 ^ 32) (q : List (BitVec 8))
    (w : Val) (h hf : Heap) (m : Mem)
    (hpre : (rb b s cap q ∗ array o [w]) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', rbPop.Returns [.ptr .u8 b, .ptr .u32 s, .u32 cap, .ptr .u8 o] m v m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ popPost b s o cap q w v h' := by
  have hinit : rbPop.initStore [.ptr .u8 b, .ptr .u32 s, .u32 cap, .ptr .u8 o] =
      some [("buf", .ptr .u8 b), ("st", .ptr .u32 s), ("cap", nu32 cap), ("out", .ptr .u8 o)] := by
    simp [Fn.initStore, rbPop, Store.empty]; repeat' constructor
  refine Fn.returns_of_swp (post := popPost b s o cap q w) hinit ?_ d hm
  obtain ⟨h₁, h₂, d₁₂, rfl, ⟨cells, head, hlen, hhead, hq, hcells, hsep⟩, hout⟩ := hpre
  have hfull : ((array b cells ∗ array s [nu32 head, nu32 q.length]) ∗ array o [w])
      (h₁.union h₂) := ⟨h₁, h₂, d₁₂, rfl, hsep, hout⟩
  have hh0 : (h₁.union h₂) (s.blk, s.off) = some (nu32 head) := by
    simpa using star_get_left hfull fun _ hp =>
      star_get_right hp (fun _ ha => array_get ha (k := 0) (by simp))
  have hh1 : (h₁.union h₂) (s.blk, s.off + 1) = some (nu32 q.length) := by
    simpa using star_get_left hfull fun _ hp =>
      star_get_right hp (fun _ ha => array_get ha (k := 1) (by simp))
  have hc32 : cap % 2 ^ 32 = cap := Nat.mod_eq_of_lt hcap
  have hh32 : head % 2 ^ 32 = head := Nat.mod_eq_of_lt (by omega)
  have hl32 : q.length % 2 ^ 32 = q.length := Nat.mod_eq_of_lt (by omega)
  simp only [rbPop, Stmt.block]
  apply swp_seq; apply swp_load'
  refine ⟨.u32, s.blk, s.off, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt], _, hh0, rfl, ?_⟩
  apply swp_seq; apply swp_load'
  refine ⟨.u32, s.blk, s.off + 1, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt], _, hh1, rfl, ?_⟩
  apply swp_ite
  cases q with
  | nil =>
    right
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, Expr.u32, Val.u32, Val.ofInt], ?_⟩
    apply swp_assign'
    simp [popPost]
    exact ⟨rfl, h₁, h₂, d₁₂, rfl, ⟨cells, head, hlen, hhead, hq, hcells, hsep⟩, hout⟩
  | cons a q' =>
    simp only [List.length_cons] at hq hl32 hh1 hfull ⊢
    left
    refine ⟨by simp [nu32, intBinOp, BitVec.ult, Expr.u32, Val.u32, Val.ofInt, hl32], ?_⟩
    -- c = buf[head]: the front element
    have hfront : cells[head]? = some (.int .u8 a) := by
      have := hcells 0 (by simp)
      rw [List.getElem_cons_zero] at this
      simpa [slot, hhead] using this
    have hhl : head < cells.length := by omega
    have hbcell : (h₁.union h₂) (b.blk, b.off + head) = some (.int .u8 a) := by
      have := star_get_left hfull fun _ hp => star_get_left hp fun _ ha => array_get ha hhl
      rw [this]; simp [List.getElem?_eq_getElem hhl] at hfront ⊢; exact hfront
    apply swp_seq; apply swp_load'
    refine ⟨.u8, b.blk, b.off + head, by simp [Expr.evalAddr, nu32, hh32], _, hbcell, rfl, ?_⟩
    -- out[0] = c
    have hocell := star_get_right hfull fun _ ha => array_get ha (k := 0) (by simp)
    have hfull1 := star_update_right (v := .int .u8 a) hfull fun _ ha =>
      ⟨array_ne_none ha (k := 0) (by simp), array_update ha (k := 0) (by simp) _⟩
    apply swp_seq; apply swp_store'
    refine ⟨.u8, o.blk, o.off, by simp [Expr.evalAddr, Expr.u32, Val.u32, Val.ofInt],
      .int .u8 a, by simp, rfl, ⟨_, by simpa using hocell⟩, ?_⟩
    simp only [List.set_cons_zero, Nat.add_zero] at hfull1
    -- the shared tail, after `head` has been advanced (and wrapped) to `slot cap head 1`
    have tail : ∀ st : Store, st.get "st" = some (.ptr .u32 s) →
        st.get "len" = some (nu32 (q'.length + 1)) →
        st.get "head" = some (nu32 (slot cap head 1)) →
        swp (.seq (.store (v "st") (.u32 0) (v "head"))
              (.seq (.store (v "st") (.u32 1) (v "len" - .u32 1)) ("ok" ::= .tt)))
          (fun st h' => ∃ v, rbPop.result.eval st = some v ∧ v.ty = rbPop.ret ∧
            popPost b s o cap (a :: q') w v h')
          st (((h₁.union h₂)).update (o.blk, o.off) (.int .u8 a)) := by
      intro st hst hlen' hhd
      have hs1 : slot cap head 1 < 2 ^ 32 := by have := slot_one_lt hhead; omega
      have hc0 := star_get_left hfull1 fun _ hp =>
        star_get_right hp (fun _ ha => array_get ha (k := 0) (by simp))
      have hfull2 := star_update_left (v := nu32 (slot cap head 1)) hfull1 fun _ hp =>
        ⟨by rw [star_get_right hp (fun _ ha => array_get ha (k := 0) (by simp))]; simp,
         star_update_right hp fun _ ha =>
          ⟨array_ne_none ha (k := 0) (by simp), array_update ha (k := 0) (by simp) _⟩⟩
      simp only [Nat.add_zero, List.set_cons_zero] at hfull2 hc0
      apply swp_seq; apply swp_store'
      refine ⟨.u32, s.blk, s.off, by simp [Expr.evalAddr, hst, Expr.u32, Val.u32, Val.ofInt],
        nu32 (slot cap head 1), by simp [hhd], rfl, ⟨_, hc0⟩, ?_⟩
      have hc1 := star_get_left hfull2 fun _ hp =>
        star_get_right hp (fun _ ha => array_get ha (k := 1) (by simp))
      have hfull3 := star_update_left (v := nu32 q'.length) hfull2 fun _ hp =>
        ⟨by rw [star_get_right hp (fun _ ha => array_get ha (k := 1) (by simp))]; simp,
         star_update_right hp fun _ ha =>
          ⟨array_ne_none ha (k := 1) (by simp), array_update ha (k := 1) (by simp) _⟩⟩
      apply swp_seq; apply swp_store'
      refine ⟨.u32, s.blk, s.off + 1, by simp [Expr.evalAddr, hst, Expr.u32, Val.u32, Val.ofInt],
        nu32 q'.length, ?_, rfl, ⟨_, by simpa using hc1⟩, ?_⟩
      · simp [hlen', nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt]
        exact bv_sub (b := 1) (by omega) (by omega)
      apply swp_assign'
      refine ⟨_, rfl, ?_⟩
      simp only [Store.get_set_same, Expr.eval_v, rbPop, popPost]
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      refine star_mono hfull3 (fun h₁' hp => ?_) (fun _ hq => hq)
      refine ⟨cells, slot cap head 1, hlen, slot_one_lt hhead, by omega, ?_, by simpa using hp⟩
      intro k hk
      rw [slot_succ hhead (by omega)]
      have := hcells (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at this
      exact this
    -- head = head + 1 (no wrap: head < cap < 2³²), then reset to 0 if it hit cap
    have hs32 : (head + 1) % 2 ^ 32 = head + 1 := Nat.mod_eq_of_lt (by omega)
    apply swp_seq; apply swp_assign'
    refine ⟨nu32 (head + 1), by simp [nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt,
      BitVec.ofNat_add_ofNat], ?_⟩
    apply swp_seq; apply swp_ite
    by_cases hw : head + 1 = cap
    · left
      refine ⟨by simp [nu32, intBinOp, hw], ?_⟩
      apply swp_assign'
      refine ⟨nu32 0, rfl, tail _ (by simp) (by simp) ?_⟩
      simp [slot, hw]
    · right
      have hne : BitVec.ofNat 32 (head + 1) ≠ BitVec.ofNat 32 cap := fun e => hw (by
        have := congrArg BitVec.toNat e; simpa [BitVec.toNat_ofNat, hs32, hc32] using this)
      refine ⟨by simp [nu32, intBinOp, hne], ?_⟩
      apply swp_skip
      refine tail _ (by simp) (by simp) ?_
      simp [slot, show head + 1 < cap by omega]

end Examples.M5
