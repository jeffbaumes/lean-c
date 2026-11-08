# Assignments

Every assignment takes **15 minutes or less** and ends in a concrete **output**: a file, a few sentences, or a passing check. Answers can go in `exercises/notes.md` (create it) or a reply to me.

- **Core track:** do these in order. Each block says which milestone it prepares you for, so it stays ahead of the code we write together.
- **Enrichment tracks:** optional deep dives. Pick by curiosity, in any order.
- Solutions live in `exercises/solutions/`. Try first, peek after 15 minutes.
- Run a Lean exercise from the repo root: `lean exercises/core/A4_Expr.lean`. The repo's `lean-toolchain` pins v4.35.0, which I've already installed via elan.

Legend: 📖 read · 🔧 hands-on · ✍️ write/think

---

## Core track

### Block A: before Milestone 1 (syntax + interpreter) and Milestone 2 (Hoare logic)

| # | Type | Assignment | Output / done when |
|---|---|---|---|
| **A1** | 📖 | Read the TL;DR and §2 of [phase1-landscape.md](phase1-landscape.md), then §0–§1 of [phase2-design.md](phase2-design.md). | One sentence: *why does goal 4 (proving codegen correct) push us toward a deep embedding?* |
| **A2** | 📖 | [Low\* paper](https://arxiv.org/abs/1703.00053), §1 and §2 only (skim the code). | Answer: (a) what is shallow and what is deep in Low\*? (b) what does KaRaMeL's user have to trust? |
| **A3** | 🔧 | [exercises/core/A3_ub.c](../exercises/core/A3_ub.c). For each of cases 1–7, **predict** defined or UB, then compile and run: `clang -std=c11 -Wall -Wextra -g -fsanitize=undefined,address -fno-sanitize-recover=all exercises/core/A3_ub.c -o /tmp/ub && for k in 1 2 3 4 5 6 7; do /tmp/ub $k; done` | Your prediction score out of 7. For each UB case, say how LC will prevent it: *typing*, *proof obligation*, or *emission rule* (design §3–§4). |
| **A4** | 🔧 | [exercises/core/A4_Expr.lean](../exercises/core/A4_Expr.lean): write `eval`, prove `constFold` correct, then answer the shallow-vs-deep question. | File compiles with no `sorry`. Your 2–3 sentences in the comment. |
| **A5** | 📖 | [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf) §7.1–7.2 (IMP commands, big-step semantics). Skip the Isabelle proof scripts and read the rules. | Write the big-step rule for `while` in your own notation, both cases. Milestone 1's `exec` will look exactly like this. |
| **A6** | 🔧 | [exercises/core/A6_BitVec.lean](../exercises/core/A6_BitVec.lean): predict, then `bv_decide`. Note which ones are false. | All true goals proved; false ones fixed, with the counterexample in a comment. |
| **A7** | ✍️ | Paper exercise. For `i := 0; s := 0; while i < n do (i := i + 1; s := s + i)` with postcondition `2s = n(n+1)`, find the invariant and write the three VCs (init, preserve, exit) by hand. Check yourself against [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf) §12.2 and §12.4. | Three implications on paper/in notes. |
| **A8** | 🔧 | [exercises/core/A8_SumLoop.lean](../exercises/core/A8_SumLoop.lean): use `mvcgen` on a Lean loop. Read the VCs it generates (`trace_state`) before supplying the invariant. | No `sorry`. Note how the generated VCs map to your A7 VCs. |
| **A9** | ✍️ | Answer the decision table in [phase2-design.md §9](phase2-design.md) (D1–D7). "Agree" is a fine answer; disagreement is better if you have a reason. | Your reply to me. **This unblocks Milestone 1.** |

### Block B: before Milestone 3 (heap, arrays, pointers, separation logic)

| # | Type | Assignment | Output / done when |
|---|---|---|---|
| **B1** | 🔧 | [exercises/core/B1_Sep.lean](../exercises/core/B1_Sep.lean): build `∗` from scratch and prove that separation implies no aliasing. | No `sorry`, plus your answer to the satisfiability question. |
| **B2** | 📖 | [Charguéraud, *Separation Logic for Sequential Programs*](https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf), §1–§3 (stop at the characteristic formulae). | State the frame rule from memory, and give one sentence on why it makes function specs *local*. |
| **B3** | 📖 | [Reynolds 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf), §1 and §2. Different notation, same ideas; the list-reversal example is the classic. | Write the separation-logic spec of `swap(p, q)` (two `↦` facts in, swapped out). |
| **B4** | 📖 | [CompCert Memory Model v2](https://inria.hal.science/hal-00703441), §1–§2. | Answer: why is a pointer `(block, offset)` rather than an integer? And why is one-past-the-end *formable* but not *dereferenceable*? |
| **B5** | ✍️ | Write (prose or pseudo-Lean) the spec of `memcpy(dst, src, n)` for LC: pre, post, and what you must say about overlap. Compare with C's `restrict` on `memcpy`. | Your spec. We'll check it against the one we prove in M3. |
| **B6** | 📖 | Certora's [LEAN.md](https://github.com/Certora/clean/blob/master/export/LEAN.md), §3 and §6.1–6.2. | Answer: what exactly does their `Triple` promise? Why does total correctness give you "no UB" for free? |

### Block C: before Milestone 4 (C printer + differential testing) and Milestone 5

| # | Type | Assignment | Output / done when |
|---|---|---|---|
| **C1** | 🔧 | Hand-write the C you'd *want* LC to emit for "sum an array of `u32` into a `u64`". Compile with `-std=c11 -Wall -Wextra -Wconversion -Werror -fsanitize=undefined,address`. | Clean compile, and a list of every cast you needed and why. |
| **C2** | 📖 | Regehr, [*A Guide to Undefined Behavior in C and C++*, part 1](https://blog.regehr.org/archives/213). | List three UB-based optimisations that could break a "plausible" emitter. |
| **C3** | 📖 | [Csmith paper](https://users.cs.utah.edu/~regehr/papers/pldi11-preprint.pdf), §1–§2. | One paragraph: how will *our* random-program tester avoid UB, compared with how Csmith does (design §7)? |
| **C4** | 🔧 | Skim [Plausible's README](https://github.com/leanprover-community/plausible). Once M4 has added Plausible to our `lakefile.toml` (it isn't in core Lean), try `example (xs : List Nat) : xs.reverse.reverse = xs := by plausible` and a deliberately false variant. | Note what a counterexample looks like and what instances a custom type needs. |
| **C5** | 📖 | [Memarian et al., POPL'19](https://www.cl.cam.ac.uk/~pes20/cerberus/cerberus-popl2019.pdf), §1–§2 (provenance examples). | Name one C idiom our block model makes *unrepresentable*, and say why that's fine for LC. |

### Block D: before Milestone 6 (codegen-correctness proof)

| # | Type | Assignment | Output / done when |
|---|---|---|---|
| **D1** | 📖 | [Concrete Semantics](https://concrete-semantics.org/concrete-semantics.pdf) §8.3–8.4 (compiling IMP and preserving semantics). | State the correctness theorem in one line, and say whether it's a forward or backward simulation. |
| **D2** | 📖 | Leroy, [*Formal Verification of a Realistic Compiler*](https://xavierleroy.org/publi/compcert-CACM.pdf) (CACM 2009), §1–§3. | One paragraph on why determinism lets you prove only *forward* simulation (compare `CCLib/Determinism.lean` in Certora's repo). |
| **D3** | ✍️ | Sketch, in pseudo-Lean, the statement "if LC `exec` runs `s` from `σ` to `σ'`, then Clight `Star Step` runs `toClight s` from `R σ` to `R σ'`". What must the relation `R` say about memory? | Your statement. It becomes the M6 theorem. |

*(Blocks C and D will be refined once we get there. If a milestone shows a gap in your understanding, I'll insert assignments.)*

---

## Enrichment tracks

Each item takes 15 minutes or less. Longer readings are split into parts.

### E-Lean: Lean craft (prioritise this if Lean tactics feel slow)
| # | Assignment |
|---|---|
| L1 | [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/), the chapter on monads (`do`-notation, `StateM`). *Output:* rewrite A8's `sumTo` with `StateM Nat` instead of `let mut`. |
| L2 | [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/), "Inductive Types" and "Induction and Recursion" (one 15-min sitting each). *Output:* prove `constFold` idempotent. |
| L3 | [`grind` reference](https://lean-lang.org/doc/reference/latest/The--grind--tactic/). *Output:* find one goal in A4–A8 that `grind` closes in one step. |
| L4 | [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/), the chapters on syntax and macros. *Output:* a `macro` so that `lc{ x + 3 * y }` elaborates to an `Expr` from A4. That's a preview of our surface syntax. |
| L5 | [`mvcgen` reference](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/) and [Markus Himmel's post](https://markushimmel.de/blog/my-first-verified-imperative-program). *Output:* verify a `for` loop that finds the max of an array. |

### E-C: C semantics, UB and the standard
| # | Assignment |
|---|---|
| C-1 | Find in a C11 draft (N1570, freely available) §6.3.1.1 (integer promotions) and §6.5.7 (shifts). *Output:* quote the sentence that makes A3 case 4 UB. |
| C-2 | Regehr's UB guide, parts 2 and 3 (the same blog series as C2). |
| C-3 | Read the ISO/IEC TS 6010 overview in Memarian et al. §5–§6 (PNVI-ae-udi). *Output:* explain "exposed" in two sentences. |
| C-4 | Read [KaRaMeL's `CStarToC11.ml`](https://github.com/FStarLang/karamel/blob/master/lib/CStarToC11.ml) for 15 minutes. *Output:* list two readability tricks we should copy. |
| C-5 | Read [Bedrock2's `ToCString.v`](https://github.com/mit-plv/bedrock2/blob/master/bedrock2/src/bedrock2/ToCString.v). *Output:* how does it avoid the integer-promotion trap? (Hint: look at which C type *all* arithmetic happens in.) |

### E-SL: separation logic and program logics
| # | Assignment |
|---|---|
| S-1 | Charguéraud's pearl, §4 onward, in 15-min chunks. |
| S-2 | Read [SPLean](https://github.com/verse-lab/splean)'s `xsimp` source and docs. *Output:* describe its cancellation algorithm in five lines. That will be our `sep_simp`. |
| S-3 | [Iris tutorial in Lean](https://logsem.github.io/iris-tutorial-lean/), first chapter. *Output:* list one thing Iris has that our logic deliberately lacks. |
| S-4 | [CN paper](https://www.cl.cam.ac.uk/~nk480/cn.pdf), §2 (overview). *Output:* how does CN decide which resources to frame automatically? |
| S-5 | [Velvet (CAV'26)](https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf), §2. *Output:* how does it split work between SMT and Lean tactics? |

### E-Prior: prior-art deep dives
| # | Assignment |
|---|---|
| P-1 | [HACL\* paper](https://eprint.iacr.org/2017/536), §1–§2. *Output:* what does "secret independence" mean, and could LC check it by typing? |
| P-2 | [Bedrock2 / Lightbulb, PLDI'21](https://adam.chlipala.net/papers/LightbulbPLDI21/LightbulbPLDI21.pdf), §1–§3. *Output:* what does their top-level theorem promise, end to end? |
| P-3 | [Fiat Cryptography, S&P'19](https://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf), §1–§2. *Output:* synthesis vs verification: which is LC doing? |
| P-4 | Browse [Certora's examples](https://github.com/Certora/clean/tree/master/export/examples) (`SwapSep.lean`, `IsSortedSep.lean`). *Output:* how long is a proof of `swap`? Compare with B3. |
| P-5 | [Aeneas paper](https://arxiv.org/abs/2206.07185), §1–§2. *Output:* how does Aeneas avoid needing separation logic at all? |

### E-AI: AI-assisted proving
| # | Assignment |
|---|---|
| AI-1 | [WybeCoder](https://arxiv.org/abs/2603.29088), abstract and §1. *Output:* which of our future VCs look like what it handles well? |
| AI-2 | [EasyProver](https://arxiv.org/abs/2610.38174), abstract and the Aegis section. *Output:* why do the authors think VERINA is saturated, and what's harder about real code? |
| AI-3 | Practical: once A8 is done, ask an AI assistant (me, or any other) to produce the invariant *without* seeing your solution. *Output:* did it get it? What did it need? |

---

## Progress log

Keep a checklist in `exercises/notes.md` if you like. I'll ask where you are at each milestone boundary and adapt.
