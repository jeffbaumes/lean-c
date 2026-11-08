# Milestone 5 walkthrough: a ring buffer, verified end to end

**Status:** done. `lake build` is green, with 0 `sorry` and 0 `native_decide`.

This is the first artifact the project was meant to produce: a small, useful piece of C, proved correct in Lean and checked against a real compiler.

## The C

[generated/examples.c](../generated/examples.c) is printed from [Examples/M5.lean](../Examples/M5.lean):

```c
bool rb_push(uint8_t *buf, uint32_t *st, uint32_t cap, uint8_t x) {
  uint32_t head;
  uint32_t len;
  uint32_t room;
  uint32_t idx;
  bool ok;
  head = st[0u];
  len = st[1u];
  if (len < cap) {
    room = (cap - head);
    if (len < room) {
      idx = (head + len);
    } else {
      idx = (len - room);
    }
    buf[idx] = x;
    st[1u] = (len + 1u);
    ok = true;
  } else {
    ok = false;
  }
  return ok;
}
```

`rb_pop` is the mirror image: read `buf[head]`, write it to `out[0]`, advance `head` and wrap it to 0 at `cap`, and decrement `len`.

LC has no structs yet, so the header `{head, len}` is a two-word array `st`. That's a readability cost, discussed below.

**No `%`.** The textbook index `(head + len) % cap` overflows `uint32_t` when `cap > 2³¹`, and then silently picks the wrong slot. Because unsigned wraparound is defined, no sanitizer would notice. The code above computes the slot by comparing with `cap - head`, which can't overflow. Exercise M5.1 has you put the `%` back: all the tests still pass, and the proof refuses it.

## The specification

The abstract model is a `List (BitVec 8)`, front first. The representation invariant:

```lean
def slot (cap head k : Nat) : Nat := if head + k < cap then head + k else head + k - cap

def rb (b s : Ptr) (cap : Nat) (q : List (BitVec 8)) : HProp := fun h =>
  ∃ cells head, cells.length = cap ∧ head < cap ∧ q.length ≤ cap ∧
    (∀ k < q.length, cells[slot cap head k]? = some (.int .u8 q[k])) ∧
    (array b cells ∗ array s [nu32 head, nu32 q.length]) h
```

**The theorems**, each holding inside any surrounding memory, with the rest of memory (`hf`) untouched:

- **`rbPush_correct`:** if `q.length < cap`, push returns `true` and the buffer now represents `q ++ [x]`. Otherwise it returns `false` and still represents `q`.
- **`rbPop_correct`:** for `q = a :: q'`, pop returns `true`, `out[0] = a`, and the buffer represents `q'`. For `q = []` it returns `false` and nothing changes.
- **`push_then_pop`** (exercise M5.3, solved): the two specs **compose**. Push then pop returns what was pushed. The proof uses only the two theorems and the frame (the `out` byte sits in push's frame), never the code.

## How the proofs go

They are about 90 lines (push) and 120 lines (pop). They follow the M3 pattern: `apply swp_seq`, `apply swp_load'`/`swp_store'`, then `simp` and a few `omega` calls.

New in M5:

- **Three-part heaps.** Pop owns `buf ∗ st ∗ out`. Reads reach through nested stars (`star_get_left (star_get_right …)`), and writes go through `star_update_left`/`star_update_right`, so the separation structure is preserved at every step. `star_update_right`, `star_mono`, `star_ne` and `array_ne_none` were added to [LC/Logic/Sep.lean](../LC/Logic/Sep.lean).
- **Branches that rejoin.**
  - In push, the two ways of computing `idx` leave *identical* goals once both are shown to produce `slot cap head len`. So the shared tail is proved once, using `rotate_left` and `all_goals`, without bullets.
  - In pop, the `head == cap` reset rejoins through a local `tail` lemma stated over any store whose `"head"` holds `slot cap head 1`.
- **Index arithmetic** is isolated in four small lemmas: `slot_lt`, `slot_inj`, `slot_one_lt` and `slot_succ`. Each is `unfold slot; split <;> omega`.

**`sep_simp` (still not written):** the bookkeeping pattern is now clear. It looks up a cell through nested stars, updates it, and re-proves `array` for the new heap. That's about a third of each proof. A tactic that searches `∗`-trees for the `array` owning an address would remove most of it. I've left it as a follow-up rather than build it under deadline.

## Testing end to end

`nice -n 19 lake exe lc ringtest 200 3` generates 200 random scripts of 40 operations each, with capacities 1–6. Each script runs **three ways**:

| | result |
|---|---|
| abstract `List` model vs. interpreter | 200/200 scripts agree |
| abstract model vs. compiled C (`-fsanitize=undefined,address`) | 8,000/8,000 lines PASS |
| abstract model vs. compiled C (`-O2`) | 8,000/8,000 lines PASS |

The oracle here is the **specification**, not the interpreter. That makes it a test of the spec, the semantics and the printer together. In the general difftest, `rb_push` and `rb_pop` also pass on random states (mostly *invalid* ones), and every stuck case is flagged by the sanitizers (40/40). For instance, `head ≥ cap` makes `buf[idx]` go out of bounds, and the interpreter and ASan agree.

## Proved · tested · trusted (end of M5)

For the claim *"`rb_push` in generated/examples.c, compiled with clang, implements a bounded FIFO push"*:

| Component | Status |
|---|---|
| LC `rb_push` meets its spec, for all capacities < 2³², all states satisfying `rb`, and inside any memory | **proved** (`rbPush_correct`) |
| the spec composes (push ∘ pop) | **proved** (`push_then_pop`) |
| interpreter = LC semantics | **proved** (M1/M3) |
| LC semantics agrees with C11 for these constructs | **tested** (difftest, ringtest), not proved |
| printer output means what the AST means | **tested**, not proved (M6) |
| `int` is 32 bits | **checked** by `_Static_assert` at compile time |
| clang compiles C correctly | **trusted** (CompCert would replace this, M6+) |
| Lean's kernel | **trusted** |

## What's missing, and why

- **`break` and early `return`:** deferred a second time. Neither the ring buffer nor any example needs them, and adding them means changing `Exec`'s type and re-proving everything. The right moment is when a target needs them, for example a parser that bails out on bad input.
- **Structs:** the `st` array works but reads worse than `rb->head`. Adding structs means struct types and field access in the syntax, plus a layout story for M6's byte-level Clight bridge. It's the most valuable language addition left.
- **`sep_simp`:** see above.

Each of these is a follow-up on its own.

## Your exercises

[exercises/core/M5_Exercises.lean](../exercises/core/M5_Exercises.lean):

- **M5.1:** put back `%`, watch the tests pass and the proof fail.
- **M5.2:** the `cap = 0` corner.
- **M5.3:** compose the specs.
- **M5.4:** list the TCB for the C.
- **M5.5 (stretch):** `rb_len`.

## Next: Milestone 6 (stretch)

Prove the code generator correct for a fragment. Translate LC's AST to Certora's Lean Clight AST, and prove that every LC execution has a matching Clight execution (forward simulation, design §6). The first step is checking whether Certora's `export/` Lean files can be depended on, both technically (Lean v4.32.1 vs our v4.35.0) and by licence.
