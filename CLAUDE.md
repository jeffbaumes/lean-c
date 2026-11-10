# lean-c: notes for Claude

LC is a small C-like language deeply embedded in Lean 4, with a formal semantics, a separation-logic program logic, proof automation (`lc_auto`), and a printer to freestanding C11. The shipped artifact is plain C; Lean is the proof layer. Start with [README.md](README.md) for the layout and [TODO.md](TODO.md) for what's next.

**To write a new verified LC function, use the `lc-program` skill** ([.claude/skills/lc-program/SKILL.md](.claude/skills/lc-program/SKILL.md)). It has the workflow (reference spec → tests → code → interpreter tests → proof), the proof skeletons, the pitfalls, and a cookbook of proof patterns.

## Hard rules

- **No `sorry`, no `native_decide`, no new axioms.** Every top-level theorem file ends with `#print axioms`; the only allowed axioms are `propext`, `Classical.choice`, `Quot.sound`.
- **No dependencies.** No Mathlib, no Batteries. Core Lean only (toolchain in `lean-toolchain`). This rules out `set`, `ring_nf`, `linarith`, `norm_num`, `tauto`, `by_contra`, `push_neg`, `swap`, `use`, `aesop`, `interval_cases`, `fin_cases`, and also `bv_decide`, which adds a native axiom (`._native.bv_decide.ax_*`). Core has `omega`, `grind`, `simp`, `decide`, `exists`, `by_cases`, `rcases`/`obtain`, `exact?`.
- **MIT licence.** Don't copy code from GPL/LGPL projects (CompCert, VST); cite ideas instead.
- **The C stays freestanding C11**: `<stdint.h>`, `<stdbool.h>`, `<limits.h>` only, no allocation, no libc.

## Commands

```bash
lake build                                   # everything: library, examples (proofs + #guard tests), tests, the lc tool
lake env lean Examples/Foo.lean              # check one file quickly (after `lake build` has built its imports)
lake exe lc check Examples.Foo                # build + #guards + proofs + axioms + small difftest, as one summary
lake exe lc emit generated/lc_examples       # regenerate the C after adding a function to Tests/Suite.lean
nice -n 19 lake exe lc difftest 100 1 <fn>   # differential test of one function: C under UBSan/ASan and -O2 vs. the interpreter
```

`#guard` failures and proof errors both fail `lake build`. `lc check` builds even when the examples don't, so use it while iterating. Run the difftest with `nice -n 19`; it compiles many C files.

## Adding a function to the project

1. `Examples/<Name>.lean`, in `namespace Examples.<Name>`, following the skill.
2. `import Examples.<Name>` in [Examples.lean](Examples.lean).
3. Add it to `difftestFns` in [Tests/Suite.lean](Tests/Suite.lean) as `suite_entry% Examples.Foo.foo` (or `suite_entry% … in prog` if it calls anything), then `lake exe lc emit generated/lc_examples` and commit the regenerated `generated/lc_examples.{h,c}`.
4. `lake exe lc check Examples.<Name>` says PASS. Run a bigger difftest, and mention it in [README.md](README.md) ("Verified programs") and the relevant doc in [docs/](docs).

## Writing style for docs and comments

Docs in `docs/` are short topic guides: what it is, how to use it, results, limits. Plain sentences, tables where they help, no marketing. Module docstrings (`/-! … -/`) open every Lean file and say what the file proves and why it's interesting. Tasks in [TODO.md](TODO.md) have IDs (`T07`), a priority (P0–P3) and area tags; refer to them by ID in commits. When finishing one, move it to "Done" with a line on where it was done, and add the follow-ups it uncovered as new tasks with new IDs (never reuse or renumber IDs).
