# TODO

Follow-on work, roughly in priority order. Each item says *why* it matters. See [docs/programs.md](docs/programs.md) for the current state.

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
