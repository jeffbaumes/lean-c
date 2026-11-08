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

**Verified programs** ([Examples/](Examples)):
- `parse_u32`, a decimal parser that calls a verified `is_digit` and detects overflow;
- binary search (`lower_bound`) and linear search with `break` (`find_first`);
- ring-buffer push/pop;
- `sum_to`, array sum and `copy_u8` (memcpy for separate buffers);
- interpreter-checked `gcd`, `popcount` and FNV-1a.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (Lean v4.35.0). There are no dependencies.

```bash
lake build
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
- `Examples/`: verified (or interpreter-checked) programs, one per file.
- `Tests/`: semantics tests (what is UB), printer stress functions, the difftest suite.
- `Tools/Main.lean`: the `lc` executable (C emission, differential and model-based testing).
- `generated/lc_examples.{h,c}`: the C printed for every example.
- `docs/`: topic guides (above), plus the original [landscape survey](docs/landscape.md), [design decisions](docs/design.md) and [learning assignments](docs/assignments.md).
- `TODO.md`: follow-on work, prioritised.
- `exercises/`: `core/` (with `sorry`s to fill in) and `solutions/`, named by topic. Run with `lake env lean exercises/core/Semantics.lean`.
