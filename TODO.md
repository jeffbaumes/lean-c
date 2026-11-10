# TODO

Follow-on work, roughly in priority order. Each item says *why* it matters. See [docs/programs.md](docs/programs.md) for the current state.

## North star

> Tell a fresh Claude session "write X in LC, and establish correctness with proofs instead of unit tests". Without much more time or effort than writing X in C with unit tests, you get Lean-verified C.

Today a verified function costs roughly 20–40 edit-and-check iterations, mostly mechanical bookkeeping, against a few for C with unit tests. The items below are ordered by how much of that gap they close.

## Agent workflow

- [x] **`lc_auto`: one tactic for the routine part of a proof.** Done: `lc_auto`, `lc_while I μ` and `lc_call` ([docs/automation.md](docs/automation.md)). `array_sum` and `find_first` are now fully automatic, and `lower_bound`, `copy_u8` and `parse_u32` leave only the problem-specific lemmas. Follow-ups:
  - Callees that own heap (`swpo_call`) in `lc_call`, and the ring buffer's custom `rb` predicate.
  - `∗`-trees in a different order or shape (reordering, array split/join), towards a full `sep_simp`.
  - Accessible names for the destructured invariant, so leftover goals are easier to close by hand.
  - Invariant/variant annotations in the AST, so `lc_while` isn't needed (the VC-generator item below).
- [x] **Spec-first workflow with reference implementations.** Write the spec as a plain Lean function (e.g. `decVal`, a `List` queue) and prove that the LC code refines it. Before proving anything, `#eval` and property-test the reference: the spec is the one thing proofs can't check, and the thing a human reviews. Done: `LC.Check` (deterministic generators and `forAll` for `#guard`), `is_sorted` written spec-first, and reference functions plus refinement theorems for `parse_u32` and `lower_bound` ([docs/spec-first.md](docs/spec-first.md)). Follow-ups:
  - Shrinking, so a failing `#guard` reports a minimal counterexample.
  - A reference-function version of the ring buffer spec (its `List` queue model is already one), and of `find_first`.
  - Fold the interpreter-vs-reference check into `lc check`.
- [x] **`CLAUDE.md` plus an "LC program" skill.** Done: [CLAUDE.md](CLAUDE.md) (hard rules, commands, how to add a function) and the `lc-program` skill ([.claude/skills/lc-program/SKILL.md](.claude/skills/lc-program/SKILL.md)): the six steps with a worked `count_eq` whose code blocks compile as written, the LC language in one table, the pitfalls (core-Lean-only tactics, `BitVec` widths, `rintro … rfl`, missing range bounds, `counterVariant` reading `"i"`), and a [cookbook](.claude/skills/lc-program/cookbook.md) (early return, `∗` postconditions, calls, custom variants, leftover-goal lemma shapes, `rotate_left`/`all_goals`, nested `star_get`/`star_update`, refinement as a corollary). Follow-ups:
  - Check the skill's code blocks in CI (extract and compile them), so it can't drift from the library.
  - Try it cold: a fresh session given only "write X in LC with proofs" (feeds the benchmark item below).
- [x] **`lake exe lc check <module>`.** One command: type-check, interpreter `#guard`s, a small low-priority difftest, and the build of the proofs, with a short readable summary. Done: [Tools/Main.lean](Tools/Main.lean), [docs/check.md](docs/check.md). Rows for build, `#guard`, proofs (`sorry` included), axioms, a source hygiene scan, and a `nice`d 30-case difftest of the module's suite functions. `lc` no longer imports the examples (they moved to a second exe, `lc-suite`), so it still runs when the module under check is broken. Suite entries record their module (`suite_entry%`). Writing it showed that seven example files had no `#print axioms`; they have one now. Follow-ups:
  - Run the interpreter-vs-reference check as its own row (with the spec-first follow-up), and report the failing input of a `forAll`.
  - Separate errors in imported modules from errors in the module itself, and stop at the first broken import.
  - Count `#guard`s from elaboration instead of a token scan (a small `#lc_guard` command, or an info message per guard).
  - A `--json` output for agents, and a `check --all`.
- [ ] **Benchmark the north star.** Pick 4–5 tasks (base64, CRC32, UTF-8 validation, a tokenizer, a bounded hash map). Have fresh sessions build each in C with unit tests and in LC with proofs, record time, tokens and iterations, and track the ratio.
- [ ] **Templates.** Starter files for common shapes (buffer loop, search, parser with early exit, stateful structure over caller storage) with the spec, invariant and proof skeleton filled in.

## Proof ergonomics (biggest gap vs. other tools)

- [ ] **`sep_simp` tactic.** (Partly in `lc_auto`: reads and writes of cells inside a `∗`-tree of arrays.) Find the `array` that owns an address inside a `∗`-tree, read or update it, and re-prove the `array` fact for the new heap. That's about a third of every heap proof today (Charguéraud's `xsimp` is the model).
- [x] **Store-fact automation.** (In `lc_auto`.) A tactic that carries `st.get x = some …` facts across assignments, and a `simp` set that turns `BitVec.ofNat` arithmetic into `Nat` arithmetic plus range side-conditions (`bv_sub`, `bv_udiv`, `bv_mul`, mods).
- [ ] **Verification-condition generator.** Loop invariants and variants as annotations, so a function's proof becomes "supply invariants, discharge pure VCs" (the Dafny/Velvet style). The printer ignores the annotations.
- [ ] **SMT or `grind` backend for the pure VCs.** Most leftover goals are linear arithmetic plus bit-vectors. Try `grind`, `bv_decide`, or an SMT bridge (lean-auto / Loom's approach).
- [ ] **Spec notation.** A `requires`/`ensures` front end that generates the `Fn.returns_of_swpo` boilerplate (the `suffices`/post-condition plumbing every proof repeats).

## Language

- [ ] **Structs.** `rb->head` instead of `st[0]`. Struct types, field load/store, by-value fields of scalar/array type, and a layout story for any future byte-level C model.
- [ ] **Sub-buffers.** Pass `p + k` as an argument, with a proof that it stays in bounds, plus an `array` split/join lemma (`arrayOf_split` in Certora's Clight port is the model).
- [ ] **Fixed-size local arrays** (`uint8_t buf[16];`). Scoped allocation and liveness (Low\*'s `push_frame`/`pop_frame`).
- [ ] **Surface syntax.** An `lc_fn` macro so programs read like C instead of hand-built ASTs.
- [ ] **Byte-level views.** `load32_le`/`store32_le` and similar (needed for crypto and parsers), as primitives with specs.
- [ ] **Recursion.** The semantics allows it; add an example and a variant-based rule for recursive calls.
- [ ] **`static` functions and per-module headers**, for linking into larger projects.

## Trust

- [ ] **Printer correctness proof (keeps the repo MIT).** Write a small Lean model of the C subset we emit (integer promotions, conversions, `p[i]`, `return`, calls) and prove `Fn.toC` correct against it. The trusted part shrinks to that model, which reads like the C11 clauses it encodes.
- [ ] **Cerberus as an independent oracle.** Run emitted C through Cerberus (BSD-2) or cerberus-lean, after checking its licence, as a second, ISO-faithful semantics in the difftest.
- [ ] **Progress theorem.** A well-typed program gets stuck *only* for value-dependent UB (overflow, bounds, division by zero, shifts, uninitialised reads). This complements type preservation.
- [ ] **Compile with CompCert** as an option, to extend the guarantee towards assembly for users who accept its licence.
- [ ] **Drop the 32-bit `int` assumption.** Choose the promotion type per target instead of `_Static_assert`ing it.

## Testing

- [ ] **Model-based tests for the new programs**, like `ringtest`: random strings vs. `decVal`, and random sorted arrays vs. a `List` lower bound. (Done in the interpreter by `#guard`s in `Examples/Refinement.lean`; still to do against the compiled C.)
- [ ] **Random program generation.** Generate well-typed LC programs, keep the ones the interpreter doesn't get stuck on, and difftest them (Csmith, inverted).
- [ ] **CI.** `lake build` plus a small, low-priority difftest on every push.

## Learning material

- [ ] Solution files for the stretch exercises: Hoare.5 (count-down sum), Sep.5 (`fill`), Ring.5 (`rb_len`), Prog.3 (`all_digits`).
