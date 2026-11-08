# The heap and separation logic

**Status:** done. `lake build` is green, with 0 `sorry` and 0 `native_decide`. The core logic (`swp_frame`, `swp_while`) and the interpreter theorems use only `propext` and `Quot.sound`. The two example proofs also pick up `Classical.choice` (via `simp`/`omega`, as in the Hoare logic).

**The headline theorems** ([Examples/ArraySum.lean](../Examples/ArraySum.lean)):

- **`arraySum_correct`**: for every pointer `p` and every list of 32-bit words `xs`, `array_sum(p, len xs)` returns their sum and leaves memory unchanged. This holds *inside any memory* that contains the array.
- **`copy_correct`**: for any two **separate** byte buffers of length `n`, `copy_u8(dst, src, n)` makes `dst` hold `src`'s bytes. `src` is unchanged, and every cell outside the two buffers is untouched.

## What changed in the language

- **[LC/Syntax.lean](../LC/Syntax.lean):**
  - `Ptr := {blk, off}`, `Ty.ptr t`, `Val.ptr t p`, plus `Ty.unit`/`Val.unit` for void functions.
  - Two new statements: `load x p i` (`x = p[i];`) and `store p i e` (`p[i] = e;`).
  - Memory is touched only by statements, so expressions stay pure.
  - There is no pointer arithmetic: `p[i]` with a `u32` index is Low\*'s `index`/`upd` style.
- **[LC/Semantics.lean](../LC/Semantics.lean):**
  - `Mem` maps block id to a list of cells. `State := {st : Store, mem : Mem}`.
  - `Exec` now runs over `State`.
  - `load` and `store` require the cell to exist (bounds and liveness) and the value to have the pointer's element type. Otherwise the program is stuck, so an out-of-bounds access is UB exactly like signed overflow.
- **Type checker:** pointer *literals* are rejected (only parameters hold pointers, so addresses can't be forged). It also checks `load`/`store` element types.
- **Ported:** interpreter soundness, determinism, stuck-soundness, type preservation, and all earlier proofs and exercises. The `sum_to` theorems now hold for *any* memory (`sumTo.Returns [.u32 n] m (.u64 (tri n)) m`).
- **Deferred to the ring buffer:** `break` and early `return`. They need an outcome type in `Exec`, and neither the separation logic target needs them. This is a deviation from the design doc's the separation logic scope.

## [LC/Logic/Sep.lean](../LC/Logic/Sep.lean): the separation logic

**Heap fragments:** `Heap := (block, index) → Option Val`. A concrete memory gives one (`Mem.heap`). `Disjoint`, `union` and `update` are the B1 exercise, scaled up.

**Assertions:**
- `P ∗ Q` holds of a fragment that splits into two disjoint parts satisfying `P` and `Q`.
- `array p xs` owns *exactly* the cells `p[0..len)`, holding `xs`.

**The key definition** is `swp s Q st h`, the local weakest precondition. It says: for every memory `m = h ⊎ hf` (any frame `hf`), `s` runs without UB to `m' = h' ⊎ hf` with `Q st' h'`. The frame is part of the definition, so:

- **The frame rule** (`swp_frame`) is a ten-line lemma: if `s` is fine on `h₁`, it's fine on `h₁ ⊎ h₂`, and `h₂` survives.
- **Owning a cell means it's in bounds.** `swp_load` and `swp_store` take `h (b, k) = some _`, which says the precondition *owns* that cell, and from that they derive that the real memory has it. Bounds checking becomes ownership.
- **Arrays:** `array_get` and `array_update` read and write an owned array. `star_get_left`, `star_get_right` and `star_update_left` reach through `∗`.

This is the "baked-in frame" style of Charguéraud's CFML/SPLean, Iris, Bedrock2, and Certora's Lean Clight `Triple`.

**One honest difference from the Hoare logic:** the rules are *implications*, not iffs, because not every fragment is the whole memory of some program. You apply them backwards (`apply swp_seq; apply swp_load'; …`) rather than letting `simp` rewrite everything. The primed variants (`swp_assign'`, `swp_load'`, `swp_store'`) put the computed value under `∃`, so `simp` can fill it in.

## The proofs

**`arraySum_correct`:**
- The invariant states only **the facts it needs** about the store (`st.get "i" = some …`), not the whole store as in the Hoare logic. `get_set` simp lemmas carry those facts across unrelated assignments, so this is the Hoare logic's ergonomic fix.
- The owned fragment never changes, because the loop only reads.
- The arithmetic is the Hoare logic's plus `psum_succ`.

**`copy_correct`:**
- The invariant is `array dst (take i ss ++ drop i ds) ∗ array src ss`.
- Each iteration reads `src[i]` through the right side of `∗` and writes `dst[i]` through the left side (`star_update_left`).
- `copy_step` proves that `(take i ss ++ drop i ds).set i ss[i] = take (i+1) ss ++ drop (i+1) ds`. That's list surgery, closed with `List.ext_getElem?` and `grind`.

**Overlap:** the `#eval` in Examples/Copy.lean runs `copy_u8` with `dst = src + 1` in one block and gets the "smear" [1,1,1]. The spec *can't be instantiated* for that call, because `∗` requires disjoint cells. That's C's `restrict` contract on `memcpy`, turned into a proof obligation on the caller (exercise Sep.2).

## Proved · tested · trusted

| Proved | Tested | Trusted |
|---|---|---|
| the interpreter and Hoare-logic results, re-proved over `State`; the separation-logic rules, including the frame rule; array sum and memcpy correct for all inputs and all surrounding memories | 37 `#guard`s, including in-bounds, out-of-bounds and missing-block cases | that `Exec` matches C11, **now including memory.** The typed-cell model is *more restrictive* than C (no byte-level reinterpretation), so proved programs are a conservative subset |

## Design notes

- **Proof size:** about 50 lines per example, mostly glue. A `sep_simp` tactic (Charguéraud's `xsimp`, design §5) would remove the `star_get_*` and `array_*` bookkeeping. I'd write it once a third heap-manipulating example makes the patterns clear.
- **Index type is fixed at `u32`.** C allows any integer index. That's fine for now, and the printer will emit `p[i]` with `uint32_t i`.
- **No allocation yet.** Buffers come from the caller. Scoped local arrays (`uint8_t buf[16];`) would need the block layout to grow and shrink, plus liveness. Low\*'s `push_frame`/`pop_frame` is the model.

## Your exercises

[exercises/core/SeparationLogic.lean](../exercises/core/SeparationLogic.lean):

- **Sep.1:** write `fill`.
- **Sep.2:** why `∗`, not `∧`.
- **Sep.3:** `∗` is associative.
- **Sep.4:** turn the frame into a fact about one cell.
- **Sep.5 (stretch):** verify `fill`. No solution file yet.
- **Sep.6:** what typed cells can't express.

Assignments **B2–B6** are the matching reading. **C1** (hand-write the C you'd want for array sum) is the bridge to docs/c-backend.md.

