---
name: lc-program
description: Write a new C function in LC (the C-like language embedded in Lean in this repo) and establish its correctness with Lean proofs instead of unit tests. Use whenever the task is to add, verify, or fix a verified LC program, write its spec, or prove an LC function correct with lc_auto / lc_while / lc_call.
---

# Writing a verified LC program

The goal: a C function whose correctness is a Lean theorem, for about the effort of C plus unit tests. The order matters. Each step is cheap and catches mistakes before the expensive one (the proof).

1. **Reference spec**: a plain Lean function computing the answer.
2. **Test the reference** with `#guard`s and random properties against an independent oracle.
3. **Code**: the LC `Fn`; `#guard` it type-checks and prints as C.
4. **Test the code against the reference** in the interpreter, on random inputs.
5. **Prove refinement** with `lc_auto` / `lc_while` / `lc_call`, plus a few problem-specific lemmas.
6. **Register** it for C emission and the difftest (see CLAUDE.md).

Read [Examples/SpecFirst.lean](../../../Examples/SpecFirst.lean) once before starting: it is all six steps for `is_sorted`, in order, and is the file to copy. [cookbook.md](cookbook.md) has proof patterns for the harder shapes (early return, calls, stores, branches).

Check a file with `lake env lean Examples/Foo.lean` (about 5–30 s) while editing a proof. Use `lake exe lc check Examples.Foo` for the whole picture: build, `#guard`s, proofs, axioms, hygiene, and a small difftest, in one summary.

## 1–2. The reference and its tests

Write the spec for obviousness, not speed, over `Nat`/`List`: `(xs.filter (· == x)).length`, `xs.Pairwise (·.toNat ≤ ·.toNat)`, `(xs.takeWhile (· < x)).length`. Compare unsigned values via `.toNat`. If the spec is a `Prop`, give it a `Decidable` instance and a `Bool` version (`decide`).

```lean
open LC LC.Check

def countRef (xs : List (BitVec 32)) (x : BitVec 32) : Nat := (xs.filter (· == x)).length

#guard countRef [] 3 = 0                         -- edge cases a reviewer would ask about
#guard countRef [3, 1, 3] 3 = 2

def genIn : Gen (List (BitVec 32) × BitVec 32) := do
  let xs ← Gen.list 8 (Gen.bvSmall 32)           -- bvSmall: small values, so ties happen
  let x ← Gen.bvSmall 32
  return (xs, x)

#guard forAll genIn fun (xs, x) => countRef xs x == xs.count x        -- independent oracle
#guard (samples genIn).any fun (xs, x) => countRef xs x > 0            -- both outcomes occur
```

- Test against something **written differently** (a library function, a slower algorithm, an algebraic law), never a restatement of the definition.
- Check with `samples` that the generator hits every branch of the spec. Uniform 32-bit values are almost never equal; use `Gen.bvSmall`, `Gen.sortedList`, `Gen.frequency`.
- When an oracle disagrees, decide which is right and record it as a `#guard` plus a comment (`String.toNat?` accepts `"1_000"`; C parsing doesn't).
- Generators: `Gen.below n`, `range lo hi`, `bool`, `bv w`, `bvSmall w`, `elements xs`, `frequency [(w, g)]`, `list maxLen g`, `vector n g`, `sortedList maxLen g`. `forAll g p (n := 200)`; debug a failure with `#eval counterexample? g p`.

**Stop and show the reference to the user** if the task's intent is ambiguous. The spec is the one thing the proof can't check.

## 3. The code

```lean
def countEq : Fn where
  name   := "count_eq"
  params := [("a", .ptr .u32), ("n", .int .u32), ("x", .int .u32)]
  locals := [("i", .int .u32), ("c", .int .u32), ("t", .int .u32)]
  body   := .block [
    "i" ::= .u32 0,
    "c" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "t" (v "a") (v "i"),                         -- t = a[i];
      .ite (v "t" ==. v "x") ("c" ::= v "c" + .u32 1) .skip,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u32
  result := v "c"                                         -- returned when the body falls off the end

#guard countEq.typeCheck                                  -- `f.typeCheck prog` if it calls others
#guard (cTranslationUnit [countEq]).isOk
```

The language, in brief (definitions in [LC/Syntax.lean](../../../LC/Syntax.lean), notation in [LC/Notation.lean](../../../LC/Notation.lean)):

| | LC | C |
|---|---|---|
| types | `.int .u8/.u16/.u32/.u64/.i8/…/.i64`, `.bool`, `.ptr .u32`, `.unit` | `uint32_t`, `bool`, `uint32_t *` |
| literals | `.u32 5`, `.u8 48`, `.tt`, `.ff`, `Expr.int .i32 (-1)` | `5u` |
| variables | `v "x"` | `x` |
| arithmetic | `+ - * / %`, `&&& ||| ^^^ <<< >>>`, `-e`, `~~~e` | |
| comparisons | `<. <=. >. >=. ==. !=.` (give `bool`) | |
| logic | `&&.`, `\|\|.`, `!.` | |
| conversion | `.cast .u32 e` (the only conversion; operands must have the *same* type) | `(uint32_t)e` |
| statements | `x ::= e`, `.block [...]`, `.ite c s₁ s₂`, `.while c s`, `.skip` | |
| memory | `.load "x" p i` (x = p[i]), `.store p i e` (p[i] = e); `i` is a `u32` | |
| control | `.brk`, `.ret e` | |
| calls | `.call (some "x") "f" [args]`, `.call none "f" [args]` | |

Rules that bite:
- **UB is stuck**: signed overflow, division by zero, shifts ≥ width, out-of-bounds, reading an unassigned local, signed casts that don't fit. Unsigned arithmetic wraps (defined, but often still a bug: write `lo + (hi - lo) / 2`).
- No implicit conversions: `v "c" - .u32 48` with `c : u8` doesn't type-check; write `.cast .u32 (v "c") - .u32 48`.
- No structs, no pointer arithmetic (`p + k`), no local arrays yet. Pass separate buffers, and keep state in a `u32` array (`st[0]`, `st[1]`) as the ring buffer does.
- **Name the loop counter `"i"`** if you want the stock variant `counterVariant n` (it reads `"i"`). Otherwise write your own variant (see `lbVar` in [Examples/Search.lean](../../../Examples/Search.lean)).
- Names must be distinct across params and locals.

## 4. The code against the reference

```lean
def runCount (xs : List (BitVec 32)) (x : BitVec 32) : Option Nat :=
  let cells := u32s xs
  match countEq.callMem [.ptr .u32 ⟨0, 0⟩, .u32 xs.length, .int .u32 x]
      [(0, if cells.isEmpty then [.u32 0] else cells)] with       -- no zero-length blocks
  | .ok (.int .u32 r, _) => some r.toNat
  | _ => none

#guard forAll genIn fun (xs, x) => runCount xs x == some (countRef xs x)
```

Memory is a list of blocks `(id, cells)`; a pointer is `⟨block, offset⟩`. Use `u8s`/`u32s` to turn lists into cells. With callees, pass the program: `f.callMem args mem (P := prog)`. If this `#guard` fails, fix the code (or the reference) now, before any proof.

## 5. The proof

The theorem says the result **is** the reference's value. Copy this skeleton; only the names, the arguments and the postcondition change.

```lean
def countInv (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ st.get "a" = some (.ptr .u32 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "x" = some (.int .u32 x) ∧ st.get "i" = some (nu32 i) ∧
    st.get "c" = some (nu32 (countRef (xs.take i) x)) ∧ h = h₀

/-- How the reference grows by one element: the lemma `lc_auto` needs for the loop step. -/
theorem countRef_take_succ (xs : List (BitVec 32)) (x : BitVec 32) (i : Nat) (hi : i < xs.length) :
    countRef (xs.take (i + 1)) x = countRef (xs.take i) x + (if xs[i] = x then 1 else 0) := by
  unfold countRef
  rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.length_append]
  by_cases hx : xs[i] = x <;> simp [hx]

theorem countEq_refines (P : Program) (p : Ptr) (xs : List (BitVec 32)) (x : BitVec 32)
    (hlen : xs.length < 2 ^ 32) (h hf : Heap) (m : Mem) (ha : array p (u32s xs) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m', countEq.Returns P [.ptr .u32 p, .u32 xs.length, .int .u32 x] m
      (nu32 (countRef xs x)) m' ∧ m'.heap = m.heap := by
  have hinit : countEq.initStore [.ptr .u32 p, .u32 xs.length, .int .u32 x] =
      some [("a", .ptr .u32 p), ("n", nu32 xs.length), ("x", .int .u32 x)] := by
    simp [Fn.initStore, countEq, Store.empty]; repeat' constructor
  suffices hbody : swp P countEq.body (fun st h' => ∃ v, countEq.result.eval st = some v ∧
      v.ty = countEq.ret ∧ (v = nu32 (countRef xs x) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swp
      (post := fun v h' => v = nu32 (countRef xs x) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (countInv p xs x h) (counterVariant xs.length) [countInv, counterVariant, countRef_take_succ]
  · simp [‹¬_›]                                  -- the `t ≠ x` branch: the `if` in the lemma

#print axioms countEq_refines                   -- must not list sorryAx
```

- **`swp` vs `swpo`.** If the body has `return` or the result comes from `.ret`, use `swpo` and `Fn.finish` (or skip the `suffices` and `refine Fn.returns_of_swpo hinit ?_ d hm` when the postcondition is already in the theorem's shape). See [cookbook.md](cookbook.md).
- **The invariant** is an `SProp` (`Store → Heap → Prop`): an `∃` over the ghost counters, a store fact `st.get "x" = some …` for **every** variable read after the loop or in the body (including parameters), the range facts the arithmetic needs (`i ≤ xs.length`), the reference applied to the processed prefix (`xs.take i`), and the heap (`h = h₀`, or an `array`/`∗` fact if the loop writes).
- **The succ lemma.** Phrase the accumulator as the reference on `xs.take i`, and prove how it extends to `xs.take (i + 1)` (`List.take_succ_eq_append_getElem`). Pass it to `lc_while` as an extra. This is the usual "lemma about the problem".
- **Extras** go to `simp`: the invariant and variant definitions always; spec-to-arithmetic lemmas (`psum_succ`, `decVal_take_succ`); definitions hiding a needed bound (`IsDigit` for `48 ≤ c`).
- **Leftover goals** come back simplified. The data `lc_auto` introduced has names you can use (the invariant's `∃ i` is `i`, a later store is `st_1`, a new heap `h_1`); hypotheses stay inaccessible. Close them with lemmas applied to `‹_›` or `(by omega)`, or `simp [‹_›]`. See what's left with `all_goals trace_state` before the bullets; see what `lc_auto` did with `set_option trace.lc_auto true in`.
- **Your variables are kept.** `lc_auto` substitutes equations between the variables it introduced, but never eliminates one that was in context when you called it (a parameter `cap`, the heap `h`). An equation such as `cs = []` stays a hypothesis: `subst_vars` it yourself if you want it gone.
- **When it stops**, it says why: `lc_auto: stuck at <statement>` and the expression it couldn't evaluate (usually a variable with no store fact, or `b = 0` not ruled out for `/`). A goal it gave up on after `lc_auto.heartbeats` (100000k by default) is left open with a warning instead of running for minutes.
- **Callees**: prove the callee's spec first as a body-level theorem (`isDigit_spec`), then `lc_call hfind spec init [extras]`. The call rule is for `swpo` goals, so a caller with a call uses `swpo` and `Fn.returns_of_swpo`. Callees that own heap need `swpo_call` by hand (cookbook).

What expressions become after `lc_auto` evaluates them (with `a b < 2^32` known, store facts `nu32 a`, `nu32 b`, `.int .u8 c`, `.int .u32 x`). Write the invariant and your lemmas in these shapes:

| LC | becomes |
|---|---|
| `v "a" + v "b"`, `*` | `BitVec.ofNat 32 (a + b)`, `BitVec.ofNat 32 (a * b)` (wraps by `ofNat`) |
| `v "a" - v "b"` | `BitVec.ofNat 32 (a - b)` if `b ≤ a` is in context, else `BitVec.ofNat 32 a - BitVec.ofNat 32 b` |
| `v "a" / v "b"`, `%` | `BitVec.ofNat 32 (a / b)`, `BitVec.ofNat 32 (a % b)`; `/` needs `b ≠ 0` in context |
| `.cast .u32 (v "c")` | `BitVec.ofNat 32 c.toNat` |
| `.u32 0 - v "x"` | `-x` |
| `v "x" >>> .u32 1`, `&&&` | `x >>> 1`, `x &&& 1#32` (bit operations stay `BitVec`) |
| `v "a" <. v "b"`, `==.`, `!=.` | `decide (a < b)`, `decide (a = b)`, `!decide (a = b)` |
| `p &&. q`, `p \|\|. q`, `!. p` | `(p && q)`, `(p \|\| q)`, `!p` on those booleans; in a branch, the hypothesis is the `Prop` (`a < b ∧ b ≠ 0`) |

## Pitfalls

- **Core Lean only.** No `set`, `ring_nf`, `linarith`, `norm_num`, `tauto`, `by_contra`, `push_neg`, `swap`, `use`, `interval_cases`. No `bv_decide` either: it adds a native axiom, which `#print axioms` and `lc check` reject. Use `omega`, `grind`, `simp`, `by_cases`, `exists`, `exfalso`, `rotate_left`, `Nat.lt_succ_iff_lt_or_eq`.
- **`BitVec` widths.** `BitVec 32` and `BitVec IntTy.u32.bits` are equal by computation only; write values as `.int .u32 bv` or `nu32 k`, never `.int .u32 (… : BitVec IntTy.u32.bits)`. When `rw` says "motive is not type correct", use `simp only` instead.
- **`rintro … rfl` / `obtain … rfl` renames.** Substitution keeps one side and drops the other, which can remove the variable you named (and later `‹_›` or names stop matching). Use `obtain rfl : i = k := by omega` with the direction you want, or keep the equation as a hypothesis.
- **Wrap-around.** Store facts are `nu32 k` (= `BitVec.ofNat 32 k`). `lc_auto` turns in-range arithmetic into `Nat` only when it can prove the range with `omega`, so put the bound (`i ≤ xs.length`, `hlen : xs.length < 2 ^ 32`, `acc < 2 ^ 32`) in the invariant or hypotheses. Leftover `% 2 ^ 32` terms mean a missing bound.
- **`omega` doesn't see through definitions.** Unfold or pass them as extras; `xs[j]?`-style facts need `List.getElem?_eq_getElem`.
- **Don't edit `LC/` to make a proof go through** unless the change is a general lemma (then add it to `LC/Spec.lean` or tag it `@[lc_simp]`, and say so).
- **`lake build` caches.** After changing an imported file, `lake env lean` on a dependent file uses the old `.olean` until you `lake build` the import.

## Done means

- `lake exe lc check Examples.Foo` says PASS (it builds the file, runs the `#guard`s, checks `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`, and difftests the function once it is in the suite).
- The reference has edge-case `#guard`s and an oracle property; the code passes the interpreter-vs-reference `#guard`.
- The function is in `Tests/Suite.lean` (`suite_entry% Examples.Foo.foo`), the C is regenerated, and `nice -n 19 lake exe lc difftest 100 1 <name>` says PASS.
- Report what the theorem says in one or two plain sentences (the reviewer reads the spec, not the proof).
