# Syntax, semantics and the interpreter

**Status:** done. `lake build` is green, with 0 `sorry` and 0 `native_decide`. Every theorem depends only on `propext` and `Quot.sound` (checked with `#print axioms`; not even `Classical.choice`).

About 860 lines in total. Read the files in this order. Each section says *what* the file is and *why* it's shaped that way.

## 1. [LC/Syntax.lean](../LC/Syntax.lean): the deep embedding

- `Width`, `IntTy`, `Ty`: the eight fixed-width integer types plus `bool`. There is no `int`: its width is implementation-defined, and "same meaning on every compiler" is the point (design §2).
- `Val.int (t : IntTy) (bv : BitVec t.bits)` is a **dependent** type. The payload's width is computed from the type tag, so an ill-sized value *cannot be constructed*. Here the type system enforces an invariant that CompCert maintains with side conditions.
- `Expr` is pure (no assignment, no calls, no memory). That one choice removes C's unspecified evaluation order from the language (Clight does the same).
- `Stmt` has `skip, assign, seq, ite, while`. `Fn` adds typed params and locals, a body, and a single result expression.

## 2. [LC/Semantics.lean](../LC/Semantics.lean): what programs mean

- **`Store`** is an association list. My first version used `Ident → Option Val`, which is nicer for proofs. A 100 000-iteration test then never finished: each update wraps a closure, so lookups walk the entire assignment history, and kernel `decide` was even worse. A first-order store fixed both.
- **Integer rule** (the heart of C's semantics): compute the *mathematical* result in `Int`, and if it isn't representable in the type, the result is `none` (UB). Unsigned arithmetic is `BitVec` wraparound. Each case cites its C11 clause. Details worth noticing:
  - `INT_MIN % -1` is UB, because C11 §6.5.5¶6 ties `%` to the representability of `/`.
  - Signed shifts are excluded entirely.
  - Conversion to a signed type that can't hold the value is *implementation-defined* in C. LC makes it stuck, so no proved program depends on it.
- **`&&` and `||` short-circuit.** `d != 0 && n / d > 1` is defined when `d = 0`. Exercise Sem.8 makes you break this and watch the tests fail.
- **`Exec`** is a big-step inductive relation. Diverging and stuck programs simply have *no* derivation, so "UB" and "no rule applies" are the same thing.

## 3. [LC/Interp.lean](../LC/Interp.lean): an executable twin, proved

- `run : Nat → Store → Stmt → Result Store` is fuel-bounded, so it's structurally recursive and needs no termination proof.
- **Three theorems:**
  - `run_sound`: `.ok` implies `Exec`.
  - `Exec.det`: the language is deterministic.
  - `run_stuck_sound`: `.stuck` implies **no** execution exists. This one needs determinism (exercise Sem.7 asks you why).
  - Together they mean the interpreter's `ok`/`stuck` answers are *facts about the semantics*. Only `outOfFuel` is uninformative.
- `Fn.call` and `Fn.call_sound` lift this to functions.

## 4. [LC/Typing.lean](../LC/Typing.lean) and [LC/Notation.lean](../LC/Notation.lean)

- The type checker is a `Bool` function: same-type operands, unsigned-only shifts, `bool` conditions, distinct names. Its soundness (type preservation) is in LC/TypingSound.lean.
- The notation is operator overloading only (`+`, `&&&`, `<.`, `::=`, `Stmt.block`), not a parser. Comparisons end in `.` because Lean's `<` must return a `Prop`.

## 5. [Examples/SumTo.lean](../Examples/SumTo.lean)

| Program | What it shows |
|---|---|
| `sumTo` | the Hoare-logic proof target; a `u64` accumulator with an explicit cast |
| `gcd`, `popcount` | `%`, masks, unsigned shifts |
| `sub32` | `INT32_MIN - 1` is `.stuck`; the `u32` version wraps |
| `ubZoo` | division by zero, `INT_MIN/-1`, `INT_MIN%-1`, shift ≥ width, `-INT8_MIN`, impl-defined cast: all stuck. Defined casts work |
| `safeDivGt1` | the short-circuit guard |
| `uninit` | type-checks, but reading it is stuck |
| `spin` | divergence is `outOfFuel`, not stuck |
| `bad` | the type checker and the dynamic semantics agree |

`theorem sumTo_10 : sumTo.Returns [.u32 10] (.u64 55)` is proved by `Fn.call_sound (by decide)`. The *kernel* runs the interpreter, and the soundness theorem turns that run into a semantic fact. That's proof by computation, with the compiler not trusted.

## Proved · tested · trusted

| Proved (Lean kernel) | Tested (`#guard`, compiled evaluation) | Trusted |
|---|---|---|
| interpreter ok ⇒ execution; stuck ⇒ no execution; determinism; two concrete program results (`sumTo_10`, `gcd_1071_462`) | ~30 behaviours across 9 programs, including every UB class | **That `Exec`/`eval` match C11.** It's checked only by reading against the cited clauses. Differential testing against real C is in docs/c-backend.md. Also the Lean kernel, and the compiled evaluator behind `#guard`/`#eval` (tests only, never proofs) |

## Your exercises

[exercises/core/Semantics.lean](../exercises/core/Semantics.lean) has 8 exercises, each 15 minutes or less. Run it with `lake env lean exercises/core/Semantics.lean`.
- Sem.1–Sem.2 write and break programs.
- Sem.3–Sem.6 are proofs, ending with interpreter completeness.
- Sem.7 is a "why", and Sem.8 is an experiment.

Sem.2 is the one I most want you to do. It finds a bug that **isn't UB**, an infinite loop caused by defined wraparound. That bug is why the Hoare logic needs *total-correctness* specs, not just "no UB".

