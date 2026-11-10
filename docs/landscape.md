# Landscape report: a Low*-style, C-emitting language in Lean 4

*Researched 2026-11-08. "Last push" dates are from the GitHub API on that day. A claim marked **(self-reported)** comes from a project's own README and was not checked independently.*

## TL;DR

1. **Nobody has built Low*/KaRaMeL in Lean 4.** I found no mature, maintained Lean 4 framework where you write low-level code in a Lean-embedded language, prove it correct, and get readable C. The closest projects are small: lean_c (10 commits, types only), Trust-Lean/AMO-Lean (verified DSL→C codegen for crypto kernels, 0–7 stars), and research prototypes.
2. **The C-semantics half of the problem appeared in Lean very recently.** In Aug–Sep 2026 [Certora/clean](https://github.com/Certora/clean) ported CompCert's **Clight** semantics and memory model to Lean 4, with an interpreter proved sound, a determinism proof and a separation logic. It has no Mathlib, no `sorry` and no `native_decide` (self-reported). The work is experimental. There is also [OathTech/cerberus-lean](https://github.com/OathTech/cerberus-lean), a Lean port of the Cerberus ISO-C semantics. It is a research prototype, tested differentially rather than proved. Both run in the **C → Lean** direction (verifying existing C). Neither runs Lean → C.
3. **The program-logic half is maturing in Lean core and its ecosystem.** Core Lean has `Std.Do` and `mvcgen`, a WP-based VC generator for monadic code. The leanprover-community project [iris-lean](https://github.com/leanprover-community/iris-lean) is active, and its paper "Iris in Lean" came out in Sep 2026. Verse Lab's Loom/Velvet is a Dafny-style verifier inside Lean. `bv_decide` is a verified bit-blaster that ships with Lean.
4. **The open gap is the Low* *direction*.** That means a verification-oriented embedded language whose proofs are erased, a printer to readable C99/C11, and an argument tying the output to a real C semantics. Point 2 suggests a strong design: make Certora's Lean Clight the **target semantics** of your emitter's correctness theorem, as CompCert's `clightgen` and VST share Clight in Rocq. Then "the emitted C is correct" becomes a Lean theorem rather than an informal argument.
5. **One strategic alternative to know about:** Rust → [Aeneas](https://github.com/AeneasVerif/aeneas) (proofs in Lean) plus Rust → [Eurydice](https://github.com/AeneasVerif/eurydice) (C output). This is how "verify in Lean, ship C" is being done in production in 2026 (SymCrypt, ML-KEM in libcrux, Signal Shot). It does *not* make your project redundant, because the C is produced by an unverified Rust→C translator, not from a Lean semantics. But it is the bar for "useful".

**Recommendation:** start fresh for the language and emitter, because there's nothing worth contributing to on that side. Plan Milestone 6 against Certora's Lean Clight rather than inventing your own C semantics. Keep milestones 1–3 dependency-free, both for learning and because Certora's fork is weeks old and may change.

---

## 1. Landscape table

| Project | Proof assistant | What it verifies | Emits C? | Status / activity (2026-11-08) | Link |
|---|---|---|---|---|---|
| **Low\* / KaRaMeL** | F\* | Low\*: F\* subset modelling C memory (HyperStack), machine ints, buffers. Proofs erased, then compiled to C | **Yes**, readable C (KaRaMeL is not verified; Low\*→C is proved on paper in the ICFP'17 paper) | Very active, last push 2026-11-06, 525★ | [repo](https://github.com/FStarLang/karamel), [tutorial](https://fstarlang.github.io/lowstar/html/) |
| **HACL\* / EverCrypt** | F\* (+ Vale for asm) | Functional correctness, memory safety and secret independence of crypto | Yes (via KaRaMeL), plus Rust | Very active, pushed 2026-11-08, 1846★ | [repo](https://github.com/hacl-star/hacl-star) |
| **Bedrock2** | Rocq (Coq) | Word-only C-like language with a byte-addressed memory (partial map word→byte), a program logic, and a verified compiler to RISC-V | Yes, via `ToCString`, which is **unverified** | Active, pushed 2026-10-23, 342★, "work in progress" | [repo](https://github.com/mit-plv/bedrock2) |
| **Fiat Cryptography** | Rocq | Synthesizes field arithmetic from specs; the pipeline is verified | Yes (also Rust, Go, Java, Bedrock2…). Ships in BoringSSL and others | Active, pushed 2026-11-06 | [repo](https://github.com/mit-plv/fiat-crypto) |
| **Jasmin** | Rocq (compiler), EasyCrypt (programs) | "Assembly in the head" language; verified compiler, constant-time | No, emits x86/ARM/RISC-V asm | Active, pushed 2026-11-07 | [repo](https://github.com/jasmin-lang/jasmin) |
| **Vale** | F\* / Dafny | Verified assembly for crypto | No, asm | Standalone repo dormant (last push 2024-02); the F\* version lives on in HACL\* | [repo](https://github.com/project-everest/vale) |
| **CompCert (Clight)** | Rocq | Verified C compiler. Clight is the simplified C used as a verification target | Consumes C (`clightgen` turns C into a Clight AST) | Active, pushed 2026-11-06. Non-commercial licence, but the semantics files are dual-LGPL | [repo](https://github.com/AbsInt/CompCert) |
| **VST** | Rocq | Separation logic for Clight, sound w.r.t. CompCert | No (verifies C) | Active, pushed 2026-11-03 | [repo](https://github.com/PrincetonUniversity/VST) |
| **RefinedC** | Rocq + Iris | Refinement and ownership types for C; Lithium automation; Caesium semantics | No (verifies C) | Ongoing work flows into RefinedRust; activity not checked | [RefinedRust](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev) |
| **Cerberus** | Lem → OCaml | Executable ISO C semantics, including the PNVI provenance models | No | Active, pushed 2026-10-30 | [repo](https://github.com/rems-project/cerberus) |
| **CN** | Cerberus-based, SMT | Separation-logic refinement types for C (POPL'23); Fulminate runtime checking (POPL'25) | No | Active (tutorial pushed 2026-11-05) | [paper](https://www.cl.cam.ac.uk/~nk480/cn.pdf) |
| **ISO/IEC TS 6010** | — | Standardized provenance model (PNVI-ae-udi) | — | **Published 2025** | [ISO](https://committee.iso.org/standard/81899.html) |
| ⭐ **Certora/clean** (CompCert fork) | **Lean 4** (v4.32.1) | Clight semantics and memory model ported from Rocq; `doStep` interpreter proved sound; determinism; separation logic (total correctness, frame rule, structs, arrays, unions, goto, function pointers); differential tests vs CompCert | **No, C → Lean** (`clightgen -lean`) | Created 2026-08-19, last push 2026-09-08, 5★, "experimental" | [repo](https://github.com/Certora/clean), [LEAN.md](https://github.com/Certora/clean/blob/master/export/LEAN.md) |
| ⭐ **cerberus-lean** | **Lean 4** | Lean port of Cerberus's ISO-C semantics, generated from Lem. Validated differentially, **not proved** equal to the OCaml | No (C → Lean) | Pushed 2026-11-07, 16★, "research prototype"; mostly written by AI agents under review by Mike Dodds | [repo](https://github.com/OathTech/cerberus-lean) |
| **Clift** | Lean 4 | AutoCorres-style C → Lean lifting (CSimpl, then monadic L1–L5) | No | Single author, 1★, last push 2026-04 | [repo](https://github.com/eisbaw/Clift) |
| **Trust-Lean / AMO-Lean** | Lean 4 | Small DSLs → Core IR → C/Rust, with simulation proofs (self-reported); e-graph optimizer for NTT/FRI kernels | **Yes** (narrow "MicroC" subset) | LambdaClass and an individual; 0–7★; AMO-Lean last push 2026-03 | [trust-lean](https://github.com/lambdaclass/trust-lean), [amo-lean](https://github.com/manuelpuebla/amo-lean) |
| **lean_c** | Lean 4 | Intends a Clight-subset Lean→C pipeline; so far only C types | Planned | 10 commits, 2★, last code 2026-02 | [repo](https://github.com/mkatkov/lean_c) |
| **LeanCP** | Lean 4 | "C memory model, operational semantics and VC generator in Lean" (progress report) | Unclear | Only a ResearchGate PDF; **no code found** | [RG](https://www.researchgate.net/publication/403194505) |
| **iris-lean** | Lean 4 | Iris base logic, proof mode (MoSeL), Diaframe-style automation | — | Active, pushed 2026-11-05, 247★; paper Sep 2026 | [repo](https://github.com/leanprover-community/iris-lean), [paper](https://arxiv.org/abs/2609.24252) |
| **SPLean** | Lean 4 | CFML-style sequential separation logic, `xsimp` | — | Last push 2026-01 | [repo](https://github.com/verse-lab/splean) |
| **Std.Do / `mvcgen`** | Lean 4 core | WP predicate transformers for monadic programs; Hoare triples; VC generation | — | In core since 4.22; documented in the reference manual | [manual](https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/) |
| **Loom / Velvet** | Lean 4 | Framework for foundational verifiers over shallow monadic embeddings; Velvet is Dafny-like, with SMT plus tactics, and proved sound | No | Active, pushed 2026-11-07; CAV'26 paper | [loom](https://github.com/verse-lab/loom), [velvet](https://github.com/verse-lab/velvet) |
| **Aeneas** (+ Charon) | Lean 4 (also others) | Safe Rust → pure functional Lean model | No | Very active, 1174★; used for SymCrypt and Signal Shot | [repo](https://github.com/AeneasVerif/aeneas) |
| **Eurydice** | — | Rust → C (successor role to KaRaMeL for Rust); unverified | **Yes** | Very active, 441★ | [repo](https://github.com/AeneasVerif/eurydice) |
| **CSLib / Boole** | Lean 4 | CS library; Boole is a Boogie-like IVL whose VCs are discharged in Lean | No | Active, 800★; Boole still early | [repo](https://github.com/leanprover/cslib), [paper](https://arxiv.org/abs/2602.04846) |
| **Strata** | Lean 4 | Dialect-based IR framework; VCs go to SMT; has CBMC/GOTO back-ends | No (has a GOTO path) | Active, pushed 2026-10-31; "breaking changes expected" | [repo](https://github.com/strata-org/Strata) |
| **LeanMLIR** | Lean 4 | SSA/MLIR peephole rewrites; LLVM integer semantics | No | Pushed 2026-07 | [repo](https://github.com/opencompl/lean-mlir) |
| **LNSym** | Lean 4 | Armv8 machine-code symbolic simulation (crypto) | No | Active, pushed 2026-11-06 | [repo](https://github.com/leanprover/LNSym) |
| **`bv_decide`** | Lean 4 core | Bit-blasting to bundled CaDiCaL with an LRAT certificate checked in Lean (trusts the compiler via `ofReduceBool`) | — | Since 4.12 (Oct 2024) | [release note](https://lean-lang.org/blog/2024-10-3-lean-4120) |
| **Lean compiler** | Lean 4 | — (unverified) | Yes, but runtime-heavy (`lean.h`, RC objects); not "readable C" | New LCNF compiler since mid-2025; C emission moved to LCNF in v4.30 | [v4.30 notes](https://lean-lang.org/doc/reference/latest/releases/v4.30.0/) |
| **AlphaProof Code** (DeepMind) | Lean 4 | Agent-written proofs (over six million lines of Lean) of security properties of Signal's *compiled* code, modelled on a Lean processor model; specs drafted with models, reviewed by people; auditing agents flag about 1% for human review | No (verifies existing code) | Announced 2026-11-10; artifacts to be open-sourced | [post](https://deepmind.google/blog/introducing-alphaproof-code/) |
| **Formalizing CPython** | Lean 4 | Agents copy CPython 3.15.2's C and Python functions into Lean line by line, test each copy against real Python on 50,000+ inputs, prove a property (or its negation), then a second agent reviews. 4,071 of 26,004 functions accepted; 418 CPython bug reports | No (models existing code) | Started 2026-10-29, post 2026-11-09 | [post](https://broyojo.com/python-formalization/), [repo](https://github.com/Broyojo/python-formalization) |
| **Axon** | Lean 4 | Toy-language → ARM64 compiler, verified core, written by Claude Code | No (asm) | Papers May–Jul 2026 | [arXiv 2605.01660](https://arxiv.org/abs/2605.01660) |

---

## 2. The most relevant projects and what to borrow

### 2.1 Low\* / KaRaMeL: the architecture to copy
- **Hybrid embedding.** Low\* is a *shallow* embedding: programs are ordinary F\* terms in an effect (`Stack`/`ST`) over a memory model (`HyperStack`). A separate *deep* step runs at extraction time: KaRaMeL takes F\*'s extracted AST (λow\*) and compiles it to C\*, then to C. The paper proves λow\* → C\* → Clight-like correct on paper; the tool itself is trusted. → **Borrow:** shallow for writing and proving, deep for emitting. In Lean the deep side is natural, because you can reflect a `def` into a syntax tree with metaprogramming or keep a deep AST with a denotation function.
- **Libraries that model C exactly.** `LowStar.Buffer` (liveness, disjointness, `modifies` clauses) and `FStar.UInt32` etc. (wraparound unsigned, signed with overflow as a precondition). → **Borrow:** the `modifies`/`loc` footprint algebra and the int-library split.
- **Readability as a requirement.** KaRaMeL keeps names, structures and inline functions so that HACL\* C passes human audit. → **Borrow:** the name-preservation and "no hidden allocation" policies.

### 2.2 Certora/clean (Lean Clight): your future target semantics
- It is already the C semantics you need for Milestone 6, in Lean, with no Mathlib. It uses `BitVec` for machine ints (exactly the representation you'd pick) and CompCert's block-based memory model with three invariants. It has an interpreter proved sound (`doStep_sound`) and a determinism theorem.
- **Borrow or reuse:** (a) emit *Clight ASTs* from your language and prove simulation into `Clight.Step`. The printed C is then trusted only through CompCert's well-tested Clight printer and `clightgen`'s parse. You can check the round trip by running `clightgen -lean` on your output and comparing ASTs (translation validation). (b) Its separation-logic design: assertions `mapsto`, `arrayOf`, `structAt`, and a triple *defined* as a statement about `Step`, so soundness holds by construction.
- **Caveats:** the fork is about 3 weeks of commits, pinned to Lean v4.32.1, and "interfaces may change". CompCert's licence: the ported semantics files (`lib/`, `common/`, `cfrontend/Clight.v`, `Ctypes.v`, `Cop.v`…) are dual-licensed under **LGPL-2.1+**. The new `export/` Lean files carry no separate licence statement that I found, so **ask Certora before depending on them**.

### 2.3 Bedrock2: the minimalist alternative
- It shows how *little* you need: one type (word), a byte-addressed memory as a partial map, no recursion, an `ExtSpec` for I/O, and an unverified C printer. The proof effort goes into the program logic and a whole-stack theorem down to RISC-V.
- **Borrow:** the omnisemantics / WP-based `exec` relation (non-determinism and UB handled uniformly), the "Live Verification" style (PLDI'24) of writing code and proof together, and the honest TCB framing ("ToCString + gcc is trusted").

### 2.4 Lean core `Std.Do` / `mvcgen` (+ Loom/Velvet): your program-logic engine
- `mvcgen` already computes WPs for `StateM`/`ExceptM` stacks and leaves loop invariants as goals. If your shallow layer is a monad over a heap, you get VC generation nearly for free. Then `omega`, `bv_decide`, `grind` or SMT can discharge the VCs.
- Velvet shows the full pattern in Lean: a shallow monadic embedding, auto-active proofs with SMT fallback, and a soundness theorem. → **Borrow:** the invariant and annotation syntax, and the "SMT first, tactic fallback" workflow.

### 2.5 Cerberus / PNVI / CN: what "no UB" must mean
- ISO/IEC TS 6010 (2025) standardizes PNVI-ae-udi provenance. You need it as a **spec of what your emitted C may rely on**, even if your own model is block-based. Example: never round-trip pointers through integers, never compare pointers across objects. A block-based model (CompCert/Low\*) is strictly more conservative, so it's safe to emit from.
- CN shows how to state C ownership specs ergonomically, and Fulminate shows how to turn them into runtime checks. → **Borrow:** compile your pre- and postconditions into optional runtime asserts in the emitted C for differential testing.
- cerberus-lean is a possible *second oracle* for differential testing (ISO semantics vs Clight semantics) later on.

### 2.6 AlphaProof Code and Formalizing CPython: agents verifying existing code at scale
Both run the opposite direction to LC. They take code that already exists (Signal's compiled code; CPython's C and Python) and model it in Lean, where LC writes new code in a verified DSL and prints C. Both rely on agents to write nearly all of the Lean, with Lean as the checker. What carries over is how they decide whether agent-written work can be trusted:
- **Specs are the weak point.** Proofs are checked by Lean, but whether a statement says anything useful isn't. CPython's early runs produced weak properties ("if it returns, the answer is ≥ 0"), and only 21% of one file's proofs held up under review. AlphaProof Code has people review every spec. → **Borrow:** a reviewer that didn't write the proof asks "could a broken version pass?" ([TODO](../TODO.md) T05), and a mutation check that makes that question mechanical (T04).
- **Known-bug sanity checks.** AlphaProof Code put two real, previously fixed bugs back into a copy of the code and got proofs that the buggy versions were insecure. → **Borrow:** the same idea as mutants that the proof must reject (T04).
- **Test before proving, then check proofs against the real system.** CPython tests every copy against real Python before proving anything, and runs accepted statements against Python again, because some accepted proofs were still wrong about real Python. → **Already here:** reference `#guard`s before the proof, and the difftest of the emitted C against the interpreter; T11 and T25 extend it.
- **Untrusted provers, trusted gatekeepers.** Both treat the proving agents as untrusted and put a small trusted step at the end (Lean plus a review). → **Already here:** `lc check` (no `sorry`, standard axioms only) is that gate; T04–T06 add the spec half.
- **List the targets up front and count.** CPython lists every function first and tracks accepted ones against the list. → **Borrow** for a larger port (T33).
- **Depth vs. breadth.** AlphaProof Code verifies compiled code, so the compiler is out of the trusted base. LC trusts its printer and the C compiler; T12 (printer proof) and T38 (CompCert) are the steps in that direction.

**Honourable mention: Aeneas + Eurydice.** Read it for its design of fixed-width integer libraries in Lean (`U32`, `I32` with `Result`-valued overflow) and for how it presents proof obligations to AI provers. Their Lean library is the most battle-tested scalar library in Lean today.

---

## 3. The open gap

| Capability | Exists in Lean 4? |
|---|---|
| Executable formal C semantics | **Yes, 2 prototypes** (Clight port, Cerberus port), both C → Lean |
| Separation logic for C in Lean | **Yes, prototype** (Certora, 1 fork) plus general frameworks (iris-lean, SPLean) |
| Hoare/WP for monadic Lean code | **Yes, in core** (`Std.Do`) |
| Write low-level code *in* Lean, prove, **emit readable C** | **No.** Only narrow DSL→C (Trust-Lean, crypto kernels) or very early (lean_c) |
| Proof that emitted C matches a C semantics | **No** in Lean (Low\*'s is on paper; Bedrock2 and Eurydice are unverified) |

So the project fills a genuine, currently unfilled slot: a **Low\*-for-Lean** whose correctness argument can, for the first time, be a *mechanized* theorem against a C semantics (Clight) in the same prover. Low\* never mechanized its own extraction, so this would be a step beyond the model you're emulating.

**Contribute or start fresh?** Start fresh for the language and emitter. There is no project to contribute to. lean_c has types only, and Trust-Lean's IR is Int/Bool with fuel semantics and no memory model. Treat Certora's Lean Clight as an *upstream dependency to target later*, and consider contributing to it once you're there.

---

## 4. AI-assisted proving: where it stands for *program* verification

- **Function-level VCs are close to solved on benchmarks.** VERINA (ICLR 2026, 189 tasks) is reported near saturation. Harmonic's Aristotle claims 96.8%; EasyProver ([arXiv 2610.38174](https://arxiv.org/abs/2610.38174), 28 Oct 2026, an off-the-shelf frontier model with no fine-tuning) resolves all 189 by proof or refutation, and 597/600 NTP4VC VCs. Numbers are self-reported and use differing metrics.
- **Real code is harder.** On EasyProver's own Aegis benchmark (Rust → Lean via Aeneas, fixed-width arithmetic and loops), only **52.7%** of statements are proved in 30 min. [VeriSoftBench](https://arxiv.org/abs/2602.18307) (repository-scale) is the other realistic benchmark.
- **Imperative, invariant-heavy code:** WybeCoder (Meta FAIR, [arXiv 2603.29088](https://arxiv.org/abs/2603.29088)) co-generates code, invariants and proofs in **Velvet**: 74% of Verina and 62% of Clever, including heapsort. LeetProof ([arXiv 2604.16584](https://arxiv.org/abs/2604.16584)) also builds on Velvet.
- **Agents building verification infrastructure:** Axon (a verified compiler written with Claude Code) and cerberus-lean (written mostly by Claude agents under expert review) show that coding agents now produce large Lean developments. Both projects stress differential testing as the guard against wrong-but-proved specs.
- **Design implication:** AI provers and automation do best on **first-order, bitvector/linear-arithmetic VCs with explicit invariants**, and worst on deep separation-logic entailments. Phase 2 should aim for a VC-generation pipeline (`mvcgen`-style) that reduces separation-logic goals to pure goals early, as CN and Velvet do.

---

## 5. Toolchain check

- **Lean stable: v4.35.0** (2026-10-12). v4.36.0-rc2 is out (2026-10-27). Certora's fork pins v4.32.1, so expect some porting if we import it later.
- Mathlib is not needed for anything above. `BitVec`, `bv_decide`, `omega`, `grind`, `Std.Do` and Plausible (leanprover-community) all work without it.

---

## 6. Reading list (in order)

**Foundations (week 1–2)**
1. Nipkow & Klein, *Concrete Semantics*, Part II (IMP, big/small step, Hoare logic, VCG). Isabelle, but the ideas map 1:1 onto Milestones 1–2. <http://concrete-semantics.org/>
2. Lean reference manual, *The `mvcgen` tactic*. <https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/>, plus Markus Himmel's walkthrough <https://markushimmel.de/blog/my-first-verified-imperative-program>

**The model to emulate (week 2–3)**
3. Protzenko et al., *Verified Low-Level Programming Embedded in F\** (ICFP 2017). **The key paper.** <https://arxiv.org/abs/1703.00053>
4. Low\* tutorial (buffers, `modifies`, machine ints, what KaRaMeL accepts). <https://fstarlang.github.io/lowstar/html/>

**Memory and separation logic (week 3–4, before Milestone 3)**
5. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures* (LICS 2002). <https://www.cs.cmu.edu/~jcr/seplogic.pdf>
6. Charguéraud, *Separation Logic for Sequential Programs* (ICFP 2020 pearl). Best hands-on intro; SPLean ports it to Lean. <https://www.chargueraud.org/research/2020/seq_seplogic/seq_seplogic.pdf>
7. Leroy, Appel, Blazy, Stewart, *The CompCert Memory Model, Version 2* (2012). <https://inria.hal.science/hal-00703441>
8. Memarian et al., *Exploring C Semantics and Pointer Provenance* (POPL 2019), the basis of TS 6010. <https://www.cl.cam.ac.uk/~pes20/cerberus/cerberus-popl2019.pdf>

**Lean-specific, directly reusable (before Milestone 4/6)**
9. Certora, *C → Lean 4: Clight semantics and a separation logic, in Lean*. <https://github.com/Certora/clean/blob/master/export/LEAN.md>
10. Velvet paper (CAV 2026). <https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf>

**Broader context (any time)**
11. Pulte et al., *CN* (POPL 2023). <https://www.cl.cam.ac.uk/~nk480/cn.pdf>
12. Ho & Protzenko, *Aeneas* (ICFP 2022). <https://arxiv.org/abs/2206.07185>
13. de Medeiros et al., *Iris in Lean* (2026). <https://arxiv.org/abs/2609.24252>
14. Bedrock2 README and the Live Verification paper (Gruetter, Fukala, Chlipala, PLDI 2024). <https://github.com/mit-plv/bedrock2>

---

## 7. Confidence notes

- **Searched hard, found nothing** for a mature Lean Low\*. The GitHub repo search and web/Zulip searches returned only the items above. Something private or unpublished could still exist (e.g., inside Certora, AWS or Harmonic).
- **Not verified:** LeanCP (no code found), Trust-Lean and AMO-Lean proof claims, the AI benchmark percentages, and RefinedC's current activity.
- **From prior knowledge, not re-checked today:** Jasmin, Vale and Fiat's backend list; the Low\* paper's proof scope.

## Sources

- KaRaMeL https://github.com/FStarLang/karamel · Low\* tutorial https://fstarlang.github.io/lowstar/html/ · Low\* paper https://arxiv.org/abs/1703.00053
- HACL\* https://github.com/hacl-star/hacl-star · Bedrock2 https://github.com/mit-plv/bedrock2 · Fiat https://github.com/mit-plv/fiat-crypto · Jasmin https://github.com/jasmin-lang/jasmin · Vale https://github.com/project-everest/vale
- CompCert https://github.com/AbsInt/CompCert · VST https://github.com/PrincetonUniversity/VST · RefinedRust https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev · Cerberus https://github.com/rems-project/cerberus · CN https://popl23.sigplan.org/details/POPL-2023-popl-research-papers/1/CN-Verifying-Systems-C-Code-with-Separation-Logic-Refinement-Types · TS 6010 https://committee.iso.org/standard/81899.html
- Certora/clean https://github.com/Certora/clean · cerberus-lean https://github.com/OathTech/cerberus-lean · ship-your-tcc (uses both) https://github.com/BasisResearch/ship-your-tcc
- Clift https://github.com/eisbaw/Clift · lean_c https://github.com/mkatkov/lean_c · Trust-Lean https://github.com/lambdaclass/trust-lean · AMO-Lean https://github.com/manuelpuebla/amo-lean · LeanCP https://www.researchgate.net/publication/403194505
- iris-lean https://github.com/leanprover-community/iris-lean · Iris in Lean https://arxiv.org/abs/2609.24252 · SPLean https://github.com/verse-lab/splean
- Std.Do/mvcgen https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic/Overview/ · Loom https://github.com/verse-lab/loom · Velvet https://github.com/verse-lab/velvet
- Aeneas https://github.com/AeneasVerif/aeneas · Eurydice https://github.com/AeneasVerif/eurydice · Rust→Lean AI report https://arxiv.org/abs/2605.30106 · SymCrypt https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/
- CSLib https://arxiv.org/abs/2602.04846 · Strata https://github.com/strata-org/Strata · LeanMLIR https://arxiv.org/abs/2407.03685 · LNSym https://github.com/leanprover/LNSym
- bv_decide https://lean-lang.org/blog/2024-10-3-lean-4120 · Lean v4.30 notes https://lean-lang.org/doc/reference/latest/releases/v4.30.0/ · Lean releases https://github.com/leanprover/lean4/releases · Plausible https://reservoir.lean-lang.org/@leanprover-community/plausible
- AlphaProof Code https://deepmind.google/blog/introducing-alphaproof-code/ · Formalizing CPython https://broyojo.com/python-formalization/
- Axon https://arxiv.org/abs/2605.01660 · EasyProver https://arxiv.org/abs/2610.38174 · WybeCoder https://arxiv.org/abs/2603.29088 · LeetProof https://arxiv.org/abs/2604.16584 · VERINA https://arxiv.org/abs/2505.23135 · Emergence AI on VeriSoftBench https://www.emergence.ai/blog/wubqc15w0squyx8mot5zn7iziw6b7x · C\* https://arxiv.org/abs/2504.02246
