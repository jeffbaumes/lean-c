# TODO

## North star

> Tell a fresh Claude session "write X in LC, and establish correctness with proofs instead of unit tests". Without much more time or effort than writing X in C with unit tests, you get Lean-verified C.

The [benchmark](docs/benchmark.md) measures the gap: single-loop buffer functions cost 6–9× the time of C with unit tests, a function with a helper call 21×, and the hard cases (ghost state, several arrays) didn't finish. The tasks below close that gap (effort), or make the result easier to trust (specs, printer, tests).

## How this list works

One flat list, most important first. Each task has:

- an **ID** (`T07`). IDs are never reused or renumbered; a finished task moves to [Done](#done) and keeps its ID. Refer to tasks by ID in commits and docs.
- a **priority**: **P0** next up, **P1** soon, **P2** later, **P3** someday.
- **area** tags:

  | tag | covers |
  |---|---|
  | `auto` | `lc_auto`, `lc_while`, `lc_call`, other tactics |
  | `check` | `lc check` and the `lc` tool |
  | `spec` | writing, testing and reviewing specs |
  | `lang` | LC language features |
  | `emit` | the C printer and generated C |
  | `trust` | shrinking or checking the trusted base |
  | `test` | testing infrastructure (interpreter, difftest, generators) |
  | `bench` | the benchmark and the example programs that come from it |
  | `ci` | continuous integration |
  | `docs` | docs, skill, cookbook, learning material |

- **Needs:** tasks that must be done first. **Helps:** tasks it makes easier, but doesn't block.

When finishing a task: tick it, move it to [Done](#done) with one line on where it was done, and add any follow-ups as new tasks with new IDs.

## Open

- [ ] **T01** · P0 · `bench` — **Finish the hash map.** It's the last benchmark task without a proof. Branch `worktree-agent-acd13f137d8365c3d` has the model, the probing reference and the invariant lemmas; the run stopped in the loop bodies of `hm_put`/`hm_get` (probing over three arrays, a wrapping index). Fix in `lc_auto` what generalises, as with tokenize.
- [ ] **T02** · P0 · `ci` — **CI.** `lake build` plus a small, `nice`d difftest on every push. Several sessions now commit to `main`, and the build is the only thing that checks them.
- [ ] **T03** · P0 · `bench` — **Re-run the benchmark with fresh sessions** on all five tasks, now that the first round of `lc_auto` fixes is in, and add the results next to the first run in [docs/benchmark.md](docs/benchmark.md). This also tries the skill cold. Needs: T01 (so what it teaches is in `lc_auto` first).
- [ ] **T04** · P1 · `spec` `check` — **Mutation check.** `lc check --mutants` makes small changes to the LC code (flip a comparison, change a constant by one, swap the branches of an `if`, drop a statement) and reports any mutant whose proof still goes through, or whose interpreter-vs-reference `#guard` still passes. A surviving mutant means the spec is too weak. Both [AlphaProof Code](https://deepmind.google/blog/introducing-alphaproof-code/) (re-introduced real bugs and proved the buggy version insecure) and the [CPython formalization](https://broyojo.com/python-formalization/) (21% of early proofs held up under review) found that agent-written specs are often weaker than they look. Needs: T06.
- [ ] **T05** · P1 · `spec` `docs` — **Spec review step.** A reviewer prompt (in the `lc-program` skill, or its own skill) for a second session that didn't write the proof. It reads only the task, the reference function, its `#guard`s and the main theorem's statement, and answers: what does the theorem promise in plain words; which hypotheses could assume the hard case away (a length bound that excludes the interesting inputs, a precondition nothing satisfies); could a broken implementation satisfy it. The verdict goes in the file's module docstring. Helps: T04.
- [ ] **T06** · P1 · `check` `spec` — **Interpreter-vs-reference as its own `lc check` row**, reporting the failing input of a `forAll`. Today it is one `#guard` among many.
- [ ] **T07** · P1 · `check` — **`#lc_guard`.** A command that counts its guards during elaboration (instead of `lc check`'s token scan) and can be switched off with an option.
- [ ] **T08** · P1 · `check` — **Proof-only check.** `lc check --proofs` skips the `#guard`s, so proof iterations don't re-run slow interpreter tests (the hashmap run lost time to this). Needs: T07.
- [ ] **T09** · P1 · `auto` — **Spec notation.** A `requires`/`ensures` front end that generates the `initStore` fact, the `suffices` and the `Fn.returns_of_swp(o)` plumbing every proof repeats (about ten lines per example).
- [ ] **T10** · P1 · `docs` — **Templates.** Starter files for common shapes (buffer loop, search, parser with early exit, structure over caller storage, nested loops), with the reference, invariant and proof skeleton filled in. Helps: T09 (the templates get shorter).
- [ ] **T11** · P1 · `test` `emit` — **Random program generation.** Generate well-typed LC programs, keep the ones the interpreter doesn't get stuck on, and difftest them (Csmith, inverted). This would have found the `if intok {` printer bug before tokenize did.
- [ ] **T12** · P1 · `trust` `emit` — **Printer correctness proof.** A small Lean model of the C subset we emit (integer promotions, conversions, `p[i]`, `return`, calls), and a proof that `Fn.toC` is correct against it. The trusted part shrinks to that model, which reads like the C11 clauses it encodes. Keeps the repo MIT: no CompCert code.
- [ ] **T13** · P1 · `auto` — **`lc_call` for callees that own heap**, via `swpo_call`: split the caller's heap, give the callee its part, frame the rest.
- [ ] **T14** · P1 · `ci` `docs` — **Check the skill's code blocks in CI** (extract and compile them), so the skill can't drift from the library. Needs: T02.
- [ ] **T15** · P2 · `auto` — **Feedback while `lc_auto` runs.** Stream the trace, or print one line per statement, so a slow run isn't silent. (The heartbeat budget, `lc_auto.heartbeats`, is done.)
- [ ] **T16** · P2 · `auto` — **A fuller `sep_simp`.** Reorder `∗`-trees, and split and join arrays, so pre, invariant and post don't have to share one tree shape (Charguéraud's `xsimp` is the model).
- [ ] **T17** · P2 · `auto` — **The ring buffer in `lc_auto`.** Its `rb` predicate is a custom `HProp`, not a `∗`-tree of arrays. Helps: T16.
- [ ] **T18** · P2 · `auto` — **Verification-condition generator.** Loop invariants and variants as annotations in the AST, so a proof is "supply invariants, discharge pure VCs" (Dafny/Velvet style) and `lc_while` isn't needed. The printer ignores the annotations.
- [ ] **T19** · P2 · `auto` — **A stronger backend for pure VCs.** Most leftover goals are linear arithmetic plus bit-vectors. Push `grind` further; `bv_decide` is out (it adds a native axiom), and SMT bridges such as lean-auto are dependencies, which the rules forbid.
- [ ] **T20** · P2 · `check` — **Separate errors in imported modules from errors in the module itself**, and stop at the first broken import.
- [ ] **T21** · P2 · `check` — **`lc check --json`** for agents, and **`lc check --all`**.
- [ ] **T22** · P2 · `spec` `test` — **Shrinking** in `LC.Check`, so a failing `#guard` reports a minimal counterexample.
- [ ] **T23** · P2 · `spec` — **Reference functions** for the ring buffer (its `List` queue model is already one) and `find_first`, with refinement theorems.
- [ ] **T24** · P2 · `test` — **Model-based tests of the compiled C** for `parse_u32` and `lower_bound`, like `ringtest`: random strings against `decVal`, random sorted arrays against a `List` lower bound. (The interpreter versions are in `Examples/Refinement.lean`.)
- [ ] **T25** · P2 · `trust` `test` — **Cerberus as a second oracle.** Run emitted C through Cerberus (BSD-2) or cerberus-lean, after checking the licence, as an ISO-faithful semantics in the difftest.
- [ ] **T26** · P2 · `lang` `emit` — **`const` pointer parameters**, so emitted prototypes match C practice (`const uint8_t *p`).
- [ ] **T27** · P2 · `lang` — **Structs.** `rb->head` instead of `st[0]`: struct types, field load/store, by-value fields of scalar or array type, and a layout story for a future byte-level model.
- [ ] **T28** · P2 · `lang` `auto` — **Sub-buffers.** Pass `p + k` as an argument, with a proof that it stays in bounds (`arrayOf_split` in Certora's Clight port is the model). Needs: T16 (array split/join).
- [ ] **T29** · P2 · `lang` — **Fixed-size local arrays** (`uint8_t buf[16];`), with scoped allocation and liveness (Low\*'s `push_frame`/`pop_frame`).
- [ ] **T30** · P2 · `lang` — **Byte-level views.** `load32_le`/`store32_le` and similar, as primitives with specs (needed for crypto and parsers).
- [ ] **T31** · P2 · `lang` — **Surface syntax.** An `lc_fn` macro so programs read like C instead of hand-built ASTs.
- [ ] **T32** · P2 · `bench` — **A less familiar benchmark task.** The five tasks are textbook functions, which favours the C arm; add one or two where the C arm also needs iterations. Helps: T03.
- [ ] **T33** · P2 · `bench` `spec` — **Port a real library, with a fixed list.** Pick a small permissively licensed freestanding C library (a byte-string or checksum library), list every function up front, port each one to LC line by line, difftest it against the original C, then prove it, and track the count. The CPython formalization's lessons apply: list the targets first, copy the code rather than the docs, test before proving, keep counterexamples instead of weakening statements. Helps: T04, T05.
- [ ] **T34** · P3 · `auto` — **Named hypotheses.** Name the conjuncts of an invariant and have `lc_auto` use those names for the hypotheses it destructures. (Data such as `i` and `st_1` already has names.)
- [ ] **T35** · P3 · `lang` `auto` — **Recursion.** The semantics allows it; add an example and a variant-based rule for recursive calls.
- [ ] **T36** · P3 · `emit` — **`static` functions and per-module headers**, for linking into larger projects.
- [ ] **T37** · P3 · `trust` — **Progress theorem.** A well-typed program gets stuck *only* for value-dependent UB (overflow, bounds, division by zero, shifts, uninitialised reads). Complements type preservation.
- [ ] **T38** · P3 · `trust` — **Compile with CompCert** as an option, extending the guarantee towards assembly for users who accept its licence.
- [ ] **T39** · P3 · `emit` `trust` — **Drop the 32-bit `int` assumption.** Choose the promotion type per target instead of `_Static_assert`ing it.
- [ ] **T40** · P3 · `docs` — **Solutions to the stretch exercises:** Hoare.5 (count-down sum), Sep.5 (`fill`), Ring.5 (`rb_len`), Prog.3 (`all_digits`).

## Done

IDs from D01 were given when this list was reorganised (2026-11-10); the details are in the docs linked.

- [x] **D01** · `auto` — `lc_auto`, `lc_while`, `lc_call`: symbolic execution, store facts, a small `sep_simp` for `∗`-trees of arrays, `BitVec` → `Nat` ([docs/automation.md](docs/automation.md)).
- [x] **D02** · `spec` — Spec-first workflow: reference functions, `LC.Check` generators and `forAll`, refinement theorems ([docs/spec-first.md](docs/spec-first.md)).
- [x] **D03** · `docs` — [CLAUDE.md](CLAUDE.md) and the `lc-program` skill with its cookbook.
- [x] **D04** · `check` — `lake exe lc check <module>` ([docs/check.md](docs/check.md)).
- [x] **D05** · `bench` — The benchmark: five tasks, C + unit tests vs. LC + proof ([docs/benchmark.md](docs/benchmark.md)).
- [x] **D06** · `bench` — crc32, utf8_valid and base64_encode merged from the benchmark's branches.
- [x] **D07** · `auto` — Benchmark fixes to `lc_auto`: `&&.`/`||.`, `lc_auto: stuck at …` errors, extras in side conditions, kept and named variables, the `lc_auto.heartbeats` budget, `%`/`==.`/`!=.` to `Nat`, `lc_call` error on `swp` goals; cookbook and skill notes (commit `db33a5b`).
- [x] **D08** · `bench` `auto` `emit` — tokenize finished ([Examples/Tokenize.lean](Examples/Tokenize.lean)); `lc_auto` leaves use plain hypotheses and decide `if`s by `omega`; printer fix for bare-variable conditions (commit `25373bc`).
