# lean-c

A small, C-like imperative language (**LC**) deeply embedded in Lean 4. It has a formal semantics, a program logic, and a code generator that prints readable, freestanding C11. It's modelled on Low\*/KaRaMeL from the F\* ecosystem. The shipped artifact is plain C; Lean is the proof layer only.

No `sorry`, no `native_decide`. MIT licensed.

## What's here

| Area | Status | Guide |
|---|---|---|
| Syntax, big-step semantics (UB = stuck), interpreter proved sound for both `ok` and `stuck`, determinism, type checker and type preservation | proved | [docs/semantics.md](docs/semantics.md) |
| Hoare logic (total correctness), defined from the semantics | proved | [docs/hoare-logic.md](docs/hoare-logic.md) |
| Heap: pointers `(block, offset)`, typed-cell arrays, bounds. Separation logic with the frame rule | proved | [docs/separation-logic.md](docs/separation-logic.md) |
| C printer (promotion-safe, freestanding C11), differential testing against the interpreter under UBSan/ASan and `-O2` | printer tested, not proved | [docs/c-backend.md](docs/c-backend.md) |
| Ring buffer proved against a queue model; the specs compose | proved, and C tested against the model | [docs/ring-buffer.md](docs/ring-buffer.md) |
| Function calls with a modular call rule, `break`, early `return`; `.h` + `.c` output | proved | [docs/programs.md](docs/programs.md) |
| `lc_auto`: one tactic for the routine part of a proof (VC generation, store facts, cells inside `∗`, `BitVec`→`Nat`, `omega`/`grind`) | five example specs re-proved with it | [docs/automation.md](docs/automation.md) |
| `lake exe lc check <module>`: build, `#guard`s, proofs, axioms, hygiene and a small difftest, summarised in one table | every example module passes | [docs/check.md](docs/check.md) |
| Spec-first workflow: reference functions, property tests in `#guard` (`LC.Check`), refinement theorems | `is_sorted` written spec-first; `parse_u32` and `lower_bound` refine reference functions | [docs/spec-first.md](docs/spec-first.md) |
| Benchmark: fresh sessions write five tasks as C + unit tests and as LC + proof | single-loop tasks 6–9× the C time; harder ones 21× or unfinished | [docs/benchmark.md](docs/benchmark.md) |

**Verified programs** ([Examples/](Examples)):
- `parse_u32`, a decimal parser that calls a verified `is_digit` and detects overflow;
- binary search (`lower_bound`) and linear search with `break` (`find_first`);
- `is_sorted`, written spec-first and proved to return exactly its reference function's value;
- `crc32` (bitwise CRC-32), `utf8_valid` (Unicode Table 3-7) and `base64_encode` (RFC 4648), each proved to refine a reference function; written by fresh sessions during the [benchmark](docs/benchmark.md);
- `tokenize`, which splits a buffer at whitespace and writes token starts and lengths into two caller arrays (up to a capacity), proved to refine a declarative reference;
- ring-buffer push/pop;
- `sum_to`, array sum and `copy_u8` (memcpy for separate buffers);
- interpreter-checked `gcd`, `popcount` and FNV-1a.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (Lean v4.35.0). There are no dependencies.

```bash
lake build
```

Check one module (build, `#guard`s, proofs, axioms, and a small difftest of its functions):

```bash
lake exe lc check Examples.SpecFirst
```

Emit C and run the testers. They need a system C compiler; override it with `LC_CC`.

```bash
lake exe lc emit generated/lc_examples      # writes .h and .c
nice -n 19 lake exe lc difftest 100 1
nice -n 19 lake exe lc ringtest 200 1
```

## Layout

- `LC/`: the language and its metatheory.
  - `Syntax`, `Semantics`, `Interp`, `Typing`, `TypingSound`, `Notation`, `Spec`.
  - `Logic/{Eval,Hoare,Sep}`: the program logics.
  - `Emit/C`: the C printer.
  - `Auto`: the `lc_auto`, `lc_while` and `lc_call` tactics.
  - `Check`: random generators and `forAll`, for property tests in `#guard`.
- `Examples/`: verified (or interpreter-checked) programs, one per file.
- `Tests/`: semantics tests (what is UB), printer stress functions, the difftest suite.
- `Tools/Main.lean`: the `lc` executable (`check`; forwards the rest to `lc-suite`). `Tools/Suite.lean`: `lc-suite` (C emission, differential and model-based testing).
- `generated/lc_examples.{h,c}`: the C printed for every example.
- `docs/`: topic guides (above), plus the original [landscape survey](docs/landscape.md), [design decisions](docs/design.md) and [learning assignments](docs/assignments.md).
- `TODO.md`: follow-on work, as one list of tasks with IDs, priorities, area tags and dependencies.
- `CLAUDE.md` and `.claude/skills/lc-program/`: instructions for Claude, and the workflow skill for writing a verified LC function (also a good human quick-start).
- `exercises/`: `core/` (with `sorry`s to fill in) and `solutions/`, named by topic. Run with `lake env lean exercises/core/Semantics.lean`.
