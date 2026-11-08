# lean-c

A small, C-like imperative language (**LC**) deeply embedded in Lean 4, with a formal semantics, a program logic, and (eventually) a code generator that prints readable C99/C11. It's modelled on Low\*/KaRaMeL from the F\* ecosystem. The shipped artifact will be plain C; Lean is the proof layer only.

This is a learning project, built milestone by milestone with a walkthrough for each.

## Status

| Milestone | What | State |
|---|---|---|
| M1 | Syntax, big-step semantics, interpreter proved sound (ok *and* stuck), type checker | ✅ [walkthrough](docs/m1-walkthrough.md) |
| M2 | Hoare logic (total correctness); `sum_to` proved correct for every `u32` input | ✅ [walkthrough](docs/m2-walkthrough.md) |
| M3 | Heap: pointers, arrays, bounds, separation logic with frame rule; array sum and `memcpy` proved | ✅ [walkthrough](docs/m3-walkthrough.md) |
| M4 | C printer (promotion-safe, freestanding C11); differential testing against the interpreter under UBSan/ASan and -O2 | ✅ [walkthrough](docs/m4-walkthrough.md) |
| M5 | Ring buffer (push/pop) proved against a queue model; specs compose; C tested against the model | ✅ [walkthrough](docs/m5-walkthrough.md) |
| M6 | (stretch) Prove code generation correct against a Lean Clight semantics | planned |

No `sorry`, no `native_decide`.

## Build

Requires [elan](https://github.com/leanprover/elan). The toolchain is pinned in `lean-toolchain` (Lean v4.35.0). There are no dependencies.

```bash
lake build
```

Exercises: `lake env lean exercises/core/M1_Exercises.lean`

Emit C and run the differential tester (needs a system C compiler; override with `LC_CC`):

```bash
lake exe lc emit generated/examples.c
lake exe lc difftest 200 1
lake exe lc ringtest 200 1
```

## Layout

- `LC/`: the language. `Syntax`, `Semantics`, `Interp`, `Typing`, `TypingSound`, `Notation`, `Logic/{Eval,Hoare,Sep}`, `Emit/C`
- `Examples/`: programs and proofs per milestone
- `Tools/Main.lean`: the `lc` executable (C emission, differential testing)
- `generated/examples.c`: the C printed for every example
- `docs/`: [landscape survey](docs/phase1-landscape.md), [design decisions](docs/phase2-design.md), [assignments](docs/assignments.md), and milestone walkthroughs
- `exercises/`: `core/` (with `sorry`s to fill in) and `solutions/`
