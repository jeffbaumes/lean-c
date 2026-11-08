# Design decisions

> **Historical note.** This is the original design document. It refers to a milestone plan (M1–M6) that has since been retired; the code is now organised by topic. See the README for current status.

*Drafted 2026-11-08 against Lean v4.35.0. Every section gives the options and their trade-offs, then a recommendation. Where a choice has a well-known precedent, it is cited. The list of decisions I need from you is in §9.*

Working name in this doc: **LC**, for "Lean-C". Rename it whenever you like.

---

## 0. The shape of the whole thing

```
 Lean user writes                LC core (deep AST, in Lean)            Shipped artifact
 ───────────────────            ─────────────────────────────           ────────────────
  lc_fn sum(a: *u32, n: u32)  ──▶  Fn { params, body : Stmt }  ──print──▶  sum.c / sum.h
    requires … ensures …           │                                       (C99/C11, <stdint.h>)
    { … }                          │ semantics: exec (relation)
                                   │ interpreter: run (function, proved sound)
                                   │ program logic: wp + triples (proved sound)
                                   ▼
                              proofs about programs  (erased: never reach C)

 Milestone 6 (stretch): ──toClight──▶ Clight AST ── Certora's Lean Clight semantics
                         prove: exec LC ⊆ Step Clight (forward simulation)
```

---

## 1. Embedding: shallow, deep, or hybrid

| | **Shallow** (Low\*, Velvet, Aeneas output) | **Deep** (Bedrock2, Clight/VST, Trust-Lean) | **Hybrid A:** shallow source, reflected to deep at emit time (Low\* + KaRaMeL) | **Hybrid B:** deep core, custom surface syntax (Bedrock2's notations) |
|---|---|---|---|---|
| Program is… | a Lean `def` in a monad | a value of an inductive `Stmt` | a Lean `def`, which a metaprogram turns into an AST | an AST written in C-like syntax via Lean macros |
| Proving programs | easiest: plain Lean reasoning, `mvcgen` works directly | needs your own WP/VC generator | easy (shallow) | needs your own WP/VC generator |
| Emitting C | needs reflection, which is unverified and part of the TCB | a plain Lean function over the AST, provable | reflection is trusted (as KaRaMeL is) | plain function, provable |
| **Codegen-correctness proof (your goal 4)** | not statable without reflection | **statable**: `print` and `toClight` are functions on data | statable only for the reflected AST, so reflection stays trusted | **statable** |
| Guarding the C subset | hard: any Lean code type-checks, so unsupported constructs fail late, at extraction | by construction: if it isn't in the AST, you can't write it | late failure (KaRaMeL's error messages are notoriously hard to read) | by construction |
| Effort to start | lowest | medium | highest (metaprogramming) | medium, plus macros |

**Recommendation: Hybrid B.** The deep core AST is the single source of truth, with a thin surface syntax added later through Lean `syntax`/`macro_rules`.
- Goal 4 needs the program as *data*, and that's what deep gives you.
- Low\* paid for its shallow embedding with a trusted extractor. That's fine for F\*, which already had extraction, but it's backwards for a project whose stated aim is to *shrink* the TCB.
- The usual objection to deep embeddings is that proving programs is painful. Bedrock2 answered it: give the deep language a **weakest-precondition function** that `simp` can unfold, so a proof about a deep program becomes ordinary Lean goals. Bedrock2 (PLDI'21) and VST's `forward` tactic both use this approach.
- In Milestones 1–2 you write ASTs by hand with a few helper notations. Real surface syntax arrives with Milestone 4 or 5, once the AST has stabilized.

*What we give up:* the `mvcgen` machinery doesn't apply directly, because it reasons about Lean monadic code, not our AST. Our own VC generator is roughly 200–400 lines and is the core of Milestone 2. That's a feature for learning. You'll still meet `mvcgen` in the exercises, because it's the best model of what our `wp` should feel like.

---

## 2. The C subset

Guiding rule: **every construct maps to C whose behaviour is fully defined once the program's proof obligations hold.** The subset is deliberately smaller than Clight.

**Types**
| In | Emitted as | Notes |
|---|---|---|
| `u8 u16 u32 u64` | `uint8_t` … `uint64_t` | wraparound, BitVec |
| `i8 i16 i32 i64` | `int8_t` … `int64_t` | overflow is a **proof obligation** (§4) |
| `bool` | `bool` (`<stdbool.h>`) | |
| `ptr τ` (to an array of τ) | `τ *` | block + offset (§3); `τ` scalar at first, struct from M5 |
| `struct` (M5) | `typedef struct { … } S;` | by-value fields of scalar or array type; no flexible arrays |
| no `int`, `long`, `char`, `size_t` | | Only fixed widths, so the result doesn't depend on the implementation |

**Statements and expressions**
- Expressions are **pure**: literals, locals, arithmetic, comparisons and logic. Memory reads and calls are *statements* (`x = *p;`, `x = f(a, b);`). This is exactly Clight's "temporaries" discipline, and it eliminates C's unspecified evaluation order by construction (precedent: CompCert's `SimplExpr` pass, Bedrock2).
- `skip; seq; x := e; if; while; *p[i] := e; x := p[i]; return; call`. `break` and early `return` arrive with M3, because they need a richer postcondition (Certora's logic uses exactly that kind of multi-outcome postcondition).
- Functions are first-order and named, with no recursion at first (Bedrock2 has the same restriction). Termination comes from loop variants in the triple (total correctness).

**Excluded, with the reason**
| Excluded | Why |
|---|---|
| varargs, `printf` | unsafe without format checking; I/O goes through declared externs |
| casts between pointer types, pointer↔int | provenance (TS 6010) and strict aliasing; the block model can't express them |
| `union`, bit-fields, `goto`, `switch` fallthrough | not needed for M1–M6; Certora handles them if we ever need them |
| floating point | rounding, NaNs, `-ffast-math`. Certora trusts the host here. Out of scope |
| implicit conversions | every width change is an explicit `cast` node with defined semantics (zero/sign extension, truncation) |
| `malloc`/`free` | "no hidden allocation". Buffers come from the caller or are fixed-size locals; a `free`-less arena could come later |
| function pointers, recursion, `volatile`, threads, `setjmp` | later if ever |

---

## 3. Memory model

| | **Flat, byte-addressed** (Bedrock2) | **Blocks of bytes** (CompCert Clight, Certora port) | **Blocks of typed cells** (Low\* buffers) |
|---|---|---|---|
| Pointer | a word | `(block, byte offset)` | `(block, element index)` |
| Memory | `word → Option byte` | `block → bytes + permissions` | `block → Array Value` (one element type per block) |
| Type punning, `memcpy` of structs | natural | natural (`encode_val`/`decode_val`) | not expressible, which suits us since we excluded it |
| Matches C's provenance rules | **no**: the model allows things C forbids, so proofs must exclude them | yes | yes, and is more conservative |
| Proof burden for simple array code | byte-level arithmetic everywhere | byte encodings everywhere | lowest: `a[i]` is a list index |
| Path to Clight (M6) | far | identity | one lemma family: a typed block simulates a Clight byte block (`encode_val`) |

**Recommendation: typed-cell blocks (Low\*-style) for M3–M5, plus a documented bridge to Clight bytes in M6.**
- `Ptr := { blk : Nat, off : Nat }`, with `Mem := Std.HashMap Nat Block` (or a function) and `Block := { ty : Ty, cells : Array Val, live : Bool }`.
- **Bounds.** Forming `p + i` requires `off + i ≤ len`; one-past-the-end is allowed, as in C11 §6.5.6. Dereferencing requires `off < len`. Out of bounds means the semantics gets **stuck**.
- **Aliasing.** Two pointers may share a block. Separation logic (§5) says when they can't. There are no casts, so strict aliasing can't be violated.
- **Liveness.** A block is created by `alloc` (a scoped local array) or provided by the caller; a dead block is stuck on access. This covers use-after-scope.
- **How UB is ruled out: both ways.**
  - *Typing* rejects ill-typed ASTs: wrong arity, width mismatches, assigning a `u32` into a `ptr`. These cases are cheap and decidable, so the type checker is a Lean function with a proved "well-typed programs don't get stuck for *type* reasons" lemma.
  - *Proof obligations* cover everything value-dependent: bounds, signed overflow, division by zero, shift amounts, liveness.
  - The semantics is *partial*: every C UB is a missing transition, so the program is stuck. A proved triple implies the program is never stuck. **"Proved" therefore means "no UB"**, with no separate UB checker to trust. This is the CompCert/VST/Certora design.

---

## 4. Integer semantics

| Option | C precedent | Pros | Cons |
|---|---|---|---|
| **Unsigned: wraparound** | C defines it | matches C exactly; `BitVec` + `bv_decide` | none |
| Signed: **overflow is a proof obligation** | Low\* `FStar.Int32`, CompCert's UB | matches C; emitted code is plain `a + b` | more VCs |
| Signed: wraparound | `-fwrapv`, Rust `wrapping_add` | fewer VCs | needs `-fwrapv` (a TCB flag) or emitting `(int32_t)((uint32_t)a + (uint32_t)b)`, which is ugly. Also relies on implementation-defined unsigned→signed conversion in C99/C11; C23 made two's complement mandatory |

**Recommendation:** unsigned arithmetic wraps; signed arithmetic carries obligations (`no_overflow`, `b ≠ 0 ∧ ¬(a = MIN ∧ b = −1)` for `/` and `%`). Shift amounts must be `< width` for every type. Also provide explicit `wrapping_*`/`checked_*` builtins on unsigned types.

- **Representation.** Values are `BitVec w` inside the semantics, which plays well with `bv_decide`, and Certora's Clight uses the same. User-facing proofs can switch to `UInt32` etc. In current Lean, `UIntN` is a structure wrapping `BitVec N` (`UInt32.toBitVec`), so the two convert for free.
- **The integer-promotion trap.** C promotes `uint8_t`/`uint16_t` operands to (signed) `int` before arithmetic, so `uint16_t a = 0xFFFF; a * a` is **signed overflow UB** (you'll see UBSan catch this in assignment A3). The fix is an emission rule: for `u8`/`u16` operations the printer emits `(uint16_t)((uint32_t)a * (uint32_t)b)`. Our semantics is "truncated `BitVec 16` multiply", and the printer is responsible for producing C that means exactly that. This is a key example of why the printer belongs in the TCB until M6.

---

## 5. Program logic

| Option | Precedent | Pros | Cons |
|---|---|---|---|
| Plain Hoare logic over the whole state | Concrete Semantics ch. 12 | simplest; ideal for M2 | with a heap, every call needs explicit "didn't touch anything else" facts |
| Hoare + `modifies`/`disjoint` clauses | **Low\*** (`LowStar.Modifies`) | SMT-friendly; no new connectives | disjointness facts grow quadratically; F\* relies on Z3, and we have no Z3 in the loop by default |
| **Separation logic** with shallow assertions (`Heap → Prop`) | Bedrock2, VST, Charguéraud's CFML/SPLean, Certora | the frame rule gives locality for free; standard for pointer code | needs entailment automation (`xsimp`-like) |
| Iris (iris-lean) | RefinedC, VST-on-Iris | the most general framework | concurrency-grade machinery we don't need; heavy dependency |

**Recommendation:** plain Hoare logic for M2 (no heap), then our **own small separation logic** for M3+, as Bedrock2 and SPLean do.
- At M2 the state is just locals, so plain Hoare logic is "separation logic with `emp` heap". The M3 upgrade then *extends* M2's logic instead of replacing it.
- Shape: a `wp : Stmt → Post → Assertion` function computed by recursion on the AST. Loops take an annotated invariant and variant, and `wp_sound` connects it to `exec`. Proving a program means `simp [wp]`, then discharging pure goals with `omega`, `bv_decide`, `grind` or `simp`.
- For M3 entailments, write a small `sep_simp` tactic: cancel matching `↦`/`array` atoms and leave pure goals. Charguéraud's `xsimp` is the reference design.
- Triples are **total correctness** (terminating and not stuck). For straight-line, loop-variant code this costs little, and it's what makes "proved ⇒ no UB" hold (§3). Certora made the same choice.
- **Stay out of `iris-lean`** unless concurrency enters scope.

---

## 6. C emission

**Readability rules** (borrowed from KaRaMeL's habits):
1. Keep user names. Rename only to avoid C keywords and reserved identifiers (`_Upper`, `__x`, `int`…), with an injective scheme. Trust-Lean proves its renaming injective, and we should do the same.
2. One LC function becomes one C function. LC loops become `while` loops. Locals are declared at first use (C99).
3. Parenthesize everything at first; a precedence-aware printer comes later (it's an easy proof target).
4. Emit a `.h` with prototypes and `static_assert`s on type widths, and a `.c` that includes only `<stdint.h>`, `<stdbool.h>` and `<stddef.h>`. All three are among the headers a freestanding implementation must provide (C11 §4¶6).
5. Optional `-DLC_CHECKS` mode: emit an `assert` for each proof obligation, as Fulminate does for CN. This is useful for differential testing.

**Rules that keep emission from adding UB:** integer promotions (§4); explicit casts for every width change; shift masks are never needed because the amount is a proof obligation; no reliance on evaluation order (§2); fixed-size local arrays only (no VLAs); no `restrict` unless we prove disjointness and want the speed.

**TCB today and how it shrinks**

| Stage | Trusted |
|---|---|
| M1–M5 | Lean kernel · *our* LC semantics (does it match C?) · printer · C compiler |
| + differential testing (M4) | the same, but "semantics matches C" and "printer is right" are *tested* on many programs under UBSan/ASan |
| M6 (stretch) | Lean kernel · Certora's Lean Clight (itself tested against CompCert) · Clight printer · C compiler. **`toClight` is proved.** |
| M6+ translation validation | parse our `.c` back with `clightgen -lean` and check that the AST equals our Clight AST. This drops the printer from the TCB |
| M6+ CompCert | compile with CompCert instead of gcc/clang, extending the guarantee to assembly (modulo the Rocq↔Lean port) |

---

## 7. Testing

Testing covers the parts we *trust*: the semantics' match to C, and the printer.

1. **Per-program differential tests (M4).** For a program `f`, generate random inputs in Lean (Plausible's `Arbitrary`/`SampleableExt`). Run the interpreter, emit `f.c` plus a generated `main` harness, compile with `clang -std=c11 -Wall -Wextra -Werror -fsanitize=undefined,address -fno-sanitize-recover=all`, run, and compare the outputs. The harness is written by Lean IO code driven by a `lake exe`.
2. **Random-program differential tests (M4+).** Generate random *well-typed* LC programs, which is easy because the AST is ours. Keep the ones the interpreter runs to completion without getting stuck, since those are UB-free by construction. Compare C against the interpreter. This is Csmith's idea (Yang et al., PLDI'11) inverted: our interpreter is the UB filter.
3. **UBSan as an oracle for the proof story.** Any sanitizer hit on a program whose interpreter run *didn't* get stuck means the semantics or the printer is wrong. That's exactly the bug class the TCB hides.
4. **Proved vs tested vs trusted.** Every milestone's README gets a three-column table with this split.

---

## 8. Proposed module layout

```
lean-c/
  lean-toolchain                 leanprover/lean4:v4.35.0
  lakefile.toml                  deps: none (Plausible added in M4)
  LC/Syntax.lean                 Ty, Val, Expr, Stmt, Fn
  LC/Semantics.lean              exec (inductive relation, big-step w/ outcomes)
  LC/Interp.lean                 run (fuel-bounded) + run_sound
  LC/Typing.lean                 typecheck + soundness for type errors
  LC/Logic/Hoare.lean            wp, triple, wp_sound          (M2)
  LC/Logic/Sep.lean              heap assertions, frame rule    (M3)
  LC/Emit/C.lean                 printer                        (M4)
  LC/Test/Diff.lean              differential harness           (M4)
  Examples/{Sum,Memcpy,Ring}.lean
  exercises/                     your assignments
```

Big-step vs small-step: **big-step with outcomes** (`normal | return v`) for M1–M5. It's simpler to prove triples against. Clight is *small-step*, so M6's simulation must bridge the two. CompCert's `ClightBigstep.v` does exactly that, and we'd port its idea.

---

## 9. Decisions I need from you

| # | Decision | My recommendation | Alternatives |
|---|---|---|---|
| D1 | Embedding | **Hybrid B: deep core, macros later** | shallow (fast start, no goal 4), Low\*-style reflection |
| D2 | Signed overflow | **proof obligation** | wraparound + `-fwrapv` |
| D3 | Memory model | **typed-cell blocks, bridged to Clight in M6** | CompCert byte blocks from day one (more faithful, ~2× proof cost in M3) |
| D4 | Logic | **Hoare (M2), then own separation logic (M3)** | Low\*-style `modifies`; iris-lean |
| D5 | Correctness | **total** (termination + no UB) | partial correctness + separate safety |
| D6 | M6 target | **Certora's Lean Clight** (after asking about the licence) | our own mini-C semantics (no external dependency, weaker claim) |
| D7 | C standard | **C11** (`static_assert`, `_Alignas` available) | C99 |

Once you reply (even "all recommendations"), I'll start **Phase 3 / Milestone 1**: syntax and interpreter for ints, locals, arithmetic, `if` and `while`.
