# TODO

Follow-on work, roughly in priority order. Each item says *why* it matters. See [docs/programs.md](docs/programs.md) for the current state.

## North star

> Tell a fresh Claude session "write X in LC, and establish correctness with proofs instead of unit tests". Without much more time or effort than writing X in C with unit tests, you get Lean-verified C.

Today a verified function costs roughly 20–40 edit-and-check iterations, mostly mechanical bookkeeping, against a few for C with unit tests. The items below are ordered by how much of that gap they close.

## Agent workflow

- [ ] **`lc_auto`: one tactic for the routine part of a proof.** Chain the VC generator, `sep_simp`, store-fact propagation, `BitVec`→`Nat` normalisation and `omega`/`grind`/`bv_decide`. Goal: a proof is the invariants, the variant, and `lc_auto`, plus the occasional arithmetic lemma (see the proof-ergonomics items below).
- [ ] **Spec-first workflow with reference implementations.** Write the spec as a plain Lean function (e.g. `decVal`, a `List` queue) and prove that the LC code refines it. Before proving anything, `#eval` and property-test the reference: the spec is the one thing proofs can't check, and the thing a human reviews.
- [ ] **`CLAUDE.md` plus an "LC program" skill.** The steps (spec → code → `lc check` → proof), the pitfalls (no Mathlib tactics: `set`, `ring_nf`, `tauto`, `by_contra`, `swap`; `BitVec` width reducibility; `rintro … rfl` renaming hypotheses), and a cookbook of proof patterns (rejoining branches with `rotate_left`/`all_goals`, calls via a callee spec, early return, loop variants, `star_get`/`star_update` through nested `∗`).
- [ ] **`lake exe lc check <module>`.** One command: type-check, interpreter `#guard`s, a small low-priority difftest, and the build of the proofs, with a short readable summary. It gives an agent fast, unambiguous feedback.
- [ ] **Benchmark the north star.** Pick 4–5 tasks (base64, CRC32, UTF-8 validation, a tokenizer, a bounded hash map). Have fresh sessions build each in C with unit tests and in LC with proofs, record time, tokens and iterations, and track the ratio.
- [ ] **Templates.** Starter files for common shapes (buffer loop, search, parser with early exit, stateful structure over caller storage) with the spec, invariant and proof skeleton filled in.

## Proof ergonomics (biggest gap vs. other tools)

- [ ] **`sep_simp` tactic.** Find the `array` that owns an address inside a `∗`-tree, read or update it, and re-prove the `array` fact for the new heap. That's about a third of every heap proof today (Charguéraud's `xsimp` is the model).
- [ ] **Store-fact automation.** A tactic that carries `st.get x = some …` facts across assignments, and a `simp` set that turns `BitVec.ofNat` arithmetic into `Nat` arithmetic plus range side-conditions (`bv_sub`, `bv_udiv`, `bv_mul`, mods).
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

- [ ] **Model-based tests for the new programs**, like `ringtest`: random strings vs. `decVal`, and random sorted arrays vs. a `List` lower bound.
- [ ] **Random program generation.** Generate well-typed LC programs, keep the ones the interpreter doesn't get stuck on, and difftest them (Csmith, inverted).
- [ ] **CI.** `lake build` plus a small, low-priority difftest on every push.

## Learning material

- [ ] Solution files for the stretch exercises: Hoare.5 (count-down sum), Sep.5 (`fill`), Ring.5 (`rb_len`), Prog.3 (`all_digits`).
