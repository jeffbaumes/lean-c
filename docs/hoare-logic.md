# Hoare logic and a verified loop

**Status:** done. `lake build` is green, with 0 `sorry` and 0 `native_decide`.

**The headline theorem** ([Examples/SumTo.lean](../Examples/SumTo.lean)):

```lean
theorem sumTo_exact (n : Nat) (hn : n < 2 ^ 32) :
    ∃ bv : BitVec 64, sumTo.Returns [.u32 n] (.int .u64 bv) ∧ bv.toNat = n * (n + 1) / 2
```

For *every* 32-bit input, `sum_to` terminates, has no UB, and returns exactly n(n+1)/2. The interpreter alone could only check `n = 10`.

The axioms are `propext`, `Quot.sound` and `Classical.choice`. `Classical.choice` is new; it comes from `omega`/`simp` lemmas, and it's standard in Lean. The logic itself (`wp_while` etc.) doesn't need it.

About 500 new lines. Read in this order:

## 1. [LC/Logic/Hoare.lean](../LC/Logic/Hoare.lean): the logic

**One definition:** `wp s Q σ := ∃ σ', Exec σ s σ' ∧ Q σ'`.

From `σ`, the statement terminates without UB in a `Q`-state, and a triple is `∀ σ, P σ → wp s Q σ`. Because the triple is *defined* from the semantics, soundness is free: there's no "the logic matches `Exec`" theorem to get wrong. This is the semantic approach used by VST, Iris, Bedrock2 and Certora's Lean Clight. *Concrete Semantics* §12 does it the other way (rules first, soundness proof after). Comparing the two is a good use of assignment A7.

**The rules are theorems:**

| | |
|---|---|
| `wp_skip`, `wp_assign`, `wp_seq`, `wp_ite` | `@[simp]`, so straight-line code is executed *by rewriting* |
| `wp_while I μ` | invariant `I` plus variant `μ : Store → Nat`; proved by strong induction on `μ` |
| `wp_not_stuck` | a proved `wp` ⇒ the interpreter can never say `stuck` (reuses `run_stuck_sound`) |
| `Triple.seq`, `Triple.while`, … | textbook-style forms, each derived in one or two lines |
| `Fn.returns_of_wp` | from a `wp` of the body to a fact about `Fn.Returns` |

`wp_assign`'s premise is `∃ v, e.eval σ = some v ∧ …`. Proving it *is* proving the expression has no UB. That's where overflow and division-by-zero obligations surface.

`wp_while`'s `hcond` obligation is that the guard itself evaluates; exercise Hoare.1 asks why it's needed.

## 2. [LC/Logic/Eval.lean](../LC/Logic/Eval.lean): making `simp` compute

These are simp lemmas so that `simp` reduces `(v "s" + .cast .u64 (v "i")).eval σ` on a concrete store all the way down to `BitVec` terms.

One snag worth knowing: `Width.bits` had to become `@[reducible]`. Without that, `BitVec 32` and `BitVec IntTy.u32.bits` are equal by computation but not *syntactically* equal, and `rw`/`simp` refused to match. Lean's error message said exactly that: "not type-correct under the implicit transparency level". Dependent types in the AST (`Val.int t (bv : BitVec t.bits)`) cost something here.

## 3. [Examples/SumTo.lean](../Examples/SumTo.lean): the proof

The proof follows A7's paper exercise:

- **Invariant:** `∃ i ≤ n, σ = [("n", n), ("i", i), ("s", tri i)]`. It states the *entire* store, which is blunt but very predictable. Separation logic (docs/separation-logic.md) lets specs mention only what matters.
- **Variant:** `n − i`.
- **Four obligations,** each a `simp`, then a little arithmetic:
  - `init`: i = 0, s = 0.
  - `cond`: the guard `i < n` never has UB.
  - `body`: run `i = i + 1; s = s + (uint64_t)i`, then show `i + 1` doesn't wrap (since i < n < 2³²), the new sum is `tri (i+1)`, and the variant decreased.
  - `exit`: the guard is false, so i = n.

**Reading the spec carefully** (exercise Hoare.6): `sumTo_correct` says the result equals `.u64 (tri n)`, which is `tri n` *mod 2⁶⁴*. A bit-vector spec can silently be about the wrapped value. `sumTo_exact` closes that gap with `tri_lt` (tri n < 2⁶⁴). This is a recurring trap in verifying C-like code. Low\* specs use `UInt32.v x` (the mathematical value) for the same reason.

`sumTo_no_ub` is the corollary that the interpreter never reports UB on any input.

## 4. [LC/TypingSound.lean](../LC/TypingSound.lean): type preservation

- `Expr.typeOf_sound`: if `e` has type τ and every initialised variable has its declared type, then any value `e` evaluates to has type τ.
- `Exec.preserves_typed`: running a well-typed statement keeps that invariant.

Together they say type errors never happen at runtime. The only ways a well-typed program gets stuck are value-dependent (overflow, division by zero, shifts, uninitialised reads), which is exactly what the logic makes you prove absent.

**Not done:** the *progress* half (a well-typed program gets stuck *only* for those reasons). It wants a precise catalogue of UB side conditions, and that's what a VC generator produces, so it fits better alongside one.

## Proved · tested · trusted

| Proved | Tested | Trusted |
|---|---|---|
| the interpreter theorems, plus: the Hoare rules (sound by construction); `sumTo` correct, exact and UB-free for **all** u32 inputs; type preservation | the `#guard`s | still: that `Exec`/`eval` match C11. Proofs are only as meaningful as the semantics they're about. Differential testing (docs/c-backend.md) is the first real check |

## Design notes

- **Specs state the whole store today.** That doesn't scale. Adding a local variable breaks the invariant's shape. The fix is separation logic, or a "frame" lemma for stores.
- **Proof effort for `sumTo`:** about 40 lines, mostly arithmetic glue (`BitVec.ofNat`, `%`). A `bv_decide`/`omega` bridge tactic would remove most of it. Worth building once we have more examples.
- **No VC generator yet.** `simp` with `wp_*` *is* a VC generator for loop-free code, and `wp_while` is applied by hand. Loop invariants as AST annotations (the Dafny/Velvet style) are a later option. They'd mean adding annotation fields that the printer ignores.

## Your exercises

[exercises/core/HoareLogic.lean](../exercises/core/HoareLogic.lean), run with `lake env lean exercises/core/HoareLogic.lean`.

- **Hoare.1:** why `hcond`.
- **Hoare.2:** swap via `simp`, then break it.
- **Hoare.3:** prove `max` with a branch.
- **Hoare.4:** prove `while (true) {}` has no total-correctness triple.
- **Hoare.5 (stretch):** count-down sum. No solution file yet; bring your attempt.
- **Hoare.6:** spec-reading.

Core assignments **B1–B6** (separation logic, the CompCert memory model, Certora's triple) are the prep for docs/separation-logic.md.

