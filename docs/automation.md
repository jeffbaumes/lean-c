# `lc_auto`: automating the routine part of a proof

`lc_auto` ([LC/Auto.lean](../LC/Auto.lean)) is one tactic for the bookkeeping in an LC proof. With it, a proof is the loop invariants, the variants, and the lemmas that are really about the problem.

## Using it

```lean
theorem arraySum_correct ... := by
  have hinit : arraySum.initStore [...] = some [...] := by ...   -- as before
  suffices hbody : swp P arraySum.body (fun st h' => ...) _ h by ...  -- as before
  lc_auto
  lc_while (sumInv p xs h) (counterVariant xs.length) [sumInv, counterVariant, psum_succ]
```

| Tactic | What it does |
|---|---|
| `lc_auto [extras]` | Symbolically executes the program in every goal, then closes what it can. It stops at `while` and at `call`. |
| `lc_while I μ [extras]` | Finds the goal about a `while` and applies the loop rule (`swp_while` or `swpo_while`) with invariant `I` and variant `μ`. It then runs `lc_auto [extras]` on the four obligations: the condition is defined, the body preserves `I` and decreases `μ`, the exit case, and the entry case. |
| `lc_call hfind spec init [extras]` | Finds the goal about a `call` and applies the modular call rule (`swpo_call_pure`). `hfind : P.find? "f" = some g` names the callee, `spec` is the callee's body proof, and `init` proves `g.initStore … = some …` (pass `_` to have it computed). Then it continues with `lc_auto [extras]`. |

`extras` are unfolded or rewritten with, the way `simp [extras]` would. Pass your invariant and variant definitions there, plus any lemma that turns a spec function into arithmetic (`psum_succ`, `decVal_take_succ`). If a definition hides a fact that the arithmetic needs, pass it too. For example, `IsDigit` holds `48 ≤ c`, and without it `c - 48` stays as unsigned wraparound.

Whatever `lc_auto` can't prove is left as a goal, already simplified, with the invariant destructured into hypotheses. The data it introduced has accessible names (the invariant's `∃ i` is `i`, a later store `st_1`, a new heap `h_1`), and the variables in context when it was called are never substituted away. The hypotheses are inaccessible, so close the goals with lemmas that take their facts as arguments, using `‹_›` or `by omega`:

```lean
  lc_while (lbInv p xs x h) lbVar [lbInv, lbVar]
  · exact sorted_below hs (by omega) ‹_›
  · exact sorted_above hs (by omega) ‹_›
```

To see what the tactic does, set `set_option trace.lc_auto true in lc_auto`.

When it can't execute a statement, it fails with `lc_auto: stuck at <statement>` and the expression `simp` couldn't reduce to a value, instead of leaving the raw `swp` goal. Each expression and each leaf goal gets a budget of `lc_auto.heartbeats` (default 100000, in thousands like `maxHeartbeats`). An expression over budget is an error; a leaf over budget is left open with a warning.

## What it automates

- **The verification-condition generator.** Rules for `skip`, assignment, `;`, `if`, load, store, `break` and `return`, for both `swp` (normal completion) and `swpo` (with outcomes). Each expression's value is computed by `simp` and fed back. An `if` turns into two goals, each with the condition as a hypothesis.
- **Store facts.** Facts `st.get x = some v` follow the store through any number of assignments. Invariants are unfolded and split into hypotheses. Equations between variables are substituted (except variables that were in context when `lc_auto` was called), and `a ≤ b` together with `b ≤ a` gives `a = b` (the usual loop exit).
- **Conditions.** Comparisons become `decide (a < b)` and `decide (a = b)` on `Nat`; `&&.` and `||.` short-circuit (`Expr.lorK`/`landK` in `LC/Logic/Eval.lean`) and become `&&`/`||` of those.
- **Side conditions** (array bounds, `simp`'s range conditions) are discharged by `omega`, then `simp [extras]` and `omega`, so a length lemma passed as an extra is seen by the bounds checks too.
- **The heap (a small `sep_simp`).** A load `p[i]` searches the `∗`-trees of `array`s in context for the array that owns the cell. A store `p[i] = e` rewrites that fact to one about the updated heap, so later loads see the new value. A final `∗` postcondition is matched part by part; only the equalities of cell lists are left over.
- **`BitVec` to `Nat`.** In-range `BitVec.ofNat` arithmetic becomes `Nat` arithmetic: `bv_sub`, `bv_udiv`, `bv_umod`, `bv_mul`, `x % 2^w = x`, `ofNat a = ofNat b ↔ a = b`, and `==`/`!=` become `decide (a = b)`. The range conditions are discharged by `omega`. You can add your own lemmas with `attribute [lc_simp] …`.
- **Existential witnesses.** In `∃ i, … ∧ st'.get "i" = some (nu32 i) ∧ …` the witness comes from unifying the store fact with what the store actually holds.
- **Leaves**, closed with `rfl`, `assumption`, `omega`, `simp`, and then `grind`. Before `grind`, a leaf is simplified once more with the plain hypotheses in context (branch conditions and bounds, anything not about a store or heap), and an `if` in it is decided when `omega` can prove or refute its condition.

## Results on the examples

[Examples/Auto.lean](../Examples/Auto.lean) proves the same specs as the hand-written proofs, with no `sorry`. The whole file checks in about 6 s.

| Program | Hand-written body proof (from unfolding the body to the end) | With `lc_auto` | What's left for the user |
|---|---|---|---|
| `array_sum` | ~34 lines | 2 lines | nothing (`psum_succ` is passed in) |
| `find_first` (`break`) | ~41 lines | 2 lines | nothing |
| `lower_bound` (binary search) | ~60 lines | 4 lines + 2 lemmas | the two uses of sortedness |
| `copy_u8` (stores through `∗`) | ~49 lines | 5 lines + 1 lemma | the list identity for one more copied byte |
| `parse_u32` (call, early returns) | ~110 lines | 11 lines + 5 lemmas | what `ParseOk` means at each exit |

The hand-written proofs in `Examples/` are kept: they show the program logic step by step.

## Limits

- **Loops and calls need you.** `lc_auto` doesn't infer invariants, variants or callee specs. `lc_call` handles callees that own no memory (`swpo_call_pure`). Callees that own part of the caller's heap still need `swpo_call` by hand.
- **Same-shape heaps only.** The final `∗` match pairs parts by position. It doesn't reorder a `∗`-tree or split arrays.
- **Arithmetic that wraps** is left as `%` terms. `lc_omega` ignores hypotheses with a `%` nested inside another `%`, because `omega` can take far too long on them. If a bound is hidden in a definition, pass the definition as an extra.
- **Hypothesis names** are inaccessible (data has names). Write the leftover reasoning as lemmas and apply them with `‹_›`.
- **Not tried yet:** the ring buffer (`Examples/RingBuffer.lean`), whose `rb` predicate is a custom `HProp` rather than a `∗`-tree of arrays.
