# Benchmark: verified LC vs. C with unit tests

How far is the north star ("verified C for about the effort of C plus unit tests")? Five tasks were each given to two fresh Claude sessions (Opus 5.5 subagents with no prior context): one writes C with unit tests, the other writes LC with a refinement proof by following [CLAUDE.md](../CLAUDE.md) and the `lc-program` skill. Run on 2026-11-09 against commit `d60d1cc`.

## Method

- **Tasks:** [bench/tasks/](../bench/tasks): `crc32`, `utf8_valid`, `base64_encode`, `tokenize`, and a bounded open-addressing `hashmap` (`hm_put`/`hm_get` over caller arrays). Both arms got the same English spec.
- **C arm:** "write it with unit tests the way you would for production code", freestanding C11, tests under ASan/UBSan. Done when the session is confident and tests pass. Sources are in [bench/c/](../bench/c).
- **LC arm:** a fresh git worktree (with a cloned `.lake`). Done when the refinement theorem is proved with no `sorry` and no non-standard axioms, `lc check` says PASS, and the function is registered for C emission. Budget: about 300 tool calls.
- **Iterations:** every compile, check or test command went through [bench/run.sh](../bench/run.sh), which logs it to `bench/logs/<arm>-<task>.log`. Commands killed by the agent aren't logged.
- **Time, tool calls, tokens:** as reported by the harness for each subagent ([bench/results.tsv](../bench/results.tsv)). The token figure is the harness's per-agent total.

## Results

| task | C: min / tool calls / iterations / tokens | LC: min / tool calls / iterations (failed) / tokens | LC status | time ratio |
|---|---|---|---|---|
| crc32 | 0.7 / 3 / 1 / 56k | 6.6 / 23 / 12 (3) / 110k | proved | 9× |
| utf8_valid | 1.5 / 4 / 2 / 59k | 9.0 / 26 / 15 (2) / 127k | proved | 6× |
| base64_encode | 1.0 / 4 / 2 / 58k | 21.0 / 56 / 27 (9) / 169k | proved | 21× |
| tokenize | 1.1 / 4 / 2 / 57k | 30.6 / 94 / 37 (21) / 252k | stopped, 10 goals left | > 28× |
| hashmap | 6.7 / 12 / 4 / 77k | 29.0 / 73 / 16 (12) / 190k | stopped, code proof not done | > 4× |

- **Single loop over a buffer** (crc32, utf8_valid): done, at 6–9× the time and 2–2.5× the tokens of the C arm. This is close to the north star.
- **A helper call, two buffers, a tail case** (base64): done, but 21×.
- **Ghost state across iterations** (tokenize: tokens found so far, current token start) **and probing over three arrays** (hashmap): neither finished within about 30 minutes, and both were stopped. In both, the pure math (the reference, the model, the invariant lemmas) went quickly. The time went into making `lc_auto` handle the loop body.
- **Every C arm passed its tests on the first run.** The tasks are well known, and the C sessions wrote strong tests: exhaustive small inputs, independent reference implementations, guard bytes, and for the hashmap a 13-mutant mutation check.
- **Cross-check** ([bench/xcheck.c](../bench/xcheck.c)): the unit-tested C and the verified LC-emitted C agree on 10⁶ random inputs (byte values biased towards UTF-8 boundaries) for crc32, utf8_valid and base64. On these tasks the proofs added assurance but did not catch a bug the tests had missed.

## What cost the LC runs their iterations

Grouped by cause. The number in brackets is how many of the five runs hit it.

| problem | runs | fix |
|---|---|---|
| `lc_auto` stops without a word on `&&.`/`\|\|.` in an `ite` or `while` condition, leaving a raw `swpo` goal | utf8, tokenize | `Expr.eval_lor`/`eval_land` simp lemmas (written on the tokenize branch); a "cannot evaluate condition" error |
| Store bounds and other side conditions (`lc_side`) use plain `simp`, not the extras passed to `lc_while`, so user length lemmas need `@[local simp]` | base64, tokenize | pass extras through to `lc_side`/`lc_disch` |
| Names: `lc_auto` makes the heap and counters inaccessible (`h✝`), and `subst_vars` removes variables such as `cap` that the invariant mentions | crc32, hashmap | accessible names (already a follow-up); an option to skip `subst_vars`; a nested-loop recipe in the cookbook |
| No feedback while slow: `lc_auto` ran for 10+ minutes with no output (wrapping multiply plus a general mask lemma); `decide` over a `String` literal never finished; invariants written with `xs.take i` hit max recursion | hashmap, base64, tokenize | a per-leaf time cap that leaves the goal unsolved; streamed trace; cookbook notes (make prefix functions opaque `f xs i` defs with `_succ` lemmas; `simp` a string to a char list before `decide`) |
| Ghost existentials in the invariant get the wrong witness, unified through the unchanged heap | tokenize | cookbook: witnesses must be functions of store values |
| `lc_call` does nothing on an `swp` goal (it needs `swpo`) | base64 | an error message; one line in the skill |
| Shapes after normalisation (`.cast .u32 b` → `BitVec.ofNat 32 b.toNat`, `0 - x` → `-x`) only visible from the trace | crc32 | a table in the skill |
| `bv_decide` adds a `._native.bv_decide.ax_*` axiom, but CLAUDE.md listed it as allowed | crc32 | fixed in CLAUDE.md and the skill |

Smaller: a goal left open that was literally a hypothesis (crc32); `if_pos`/`if_neg` deprecated in this toolchain (utf8); every check re-runs the slow `#guard`s, so proof iterations are slower than they need to be (hashmap); LC has no `const`, so the emitted prototypes take `uint8_t *` (crc32, base64).

## Limits

- One run per cell, so the ratios are rough. Expect noise of about ±2×.
- Three or four LC runs shared an 8-core machine, so their wall-clock times include contention.
- The hashmap LC run was started after the crc32 run reported the `bv_decide` axiom, and was told about it.
- The C tasks are textbook functions. A less familiar task would probably need more C iterations, and would shrink the ratio.

## Re-running

Write a task spec in `bench/tasks/`, start two fresh sessions with the prompts in [bench/prompts.md](../bench/prompts.md) (route commands through `bench/run.sh <arm>-<task>`), and add a row to `bench/results.tsv`. The completed LC examples (`Examples/Crc32.lean`, `Utf8.lean`, `Base64.lean`) were produced on side branches and are candidates for merging into `Examples/`.
