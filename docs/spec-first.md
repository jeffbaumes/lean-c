# Spec first: reference functions, property tests, refinement proofs

A proof shows that the code meets the spec. Nothing shows that the spec says what you meant. So the spec should be the easiest thing to read and the first thing tested. The workflow:

1. **Reference.** Write the spec as a plain Lean function that computes the answer, written to be obviously right rather than fast: `xs.Pairwise (· ≤ ·)`, `(xs.takeWhile (· < x)).length`, `decVal`, a `List` queue.
2. **Test the reference.** Add `#guard`s for the edge cases a reviewer would ask about. Then add random properties, ideally against an *independent oracle* (`List.mergeSort`, `String.toNat?`, `List.filter`).
3. **Code.** Write the LC function, `#guard f.typeCheck`.
4. **Test the code against the reference** on random inputs, in the interpreter: `#guard forAll gen fun a => run f a == some (ref a)`.
5. **Prove refinement**: the function returns *exactly* what the reference computes. With `lc_auto` that's usually an invariant and a few lemmas.

Steps 2 and 4 cost a few lines and seconds. They run at elaboration time, so a failing test fails `lake build`, and they catch most mistakes before any proof effort is spent.

## The tools ([LC/Check.lean](../LC/Check.lean))

All of it is pure and deterministic (a fixed seed), so it works inside `#guard`.

| | |
|---|---|
| `Gen α` | a random generator (a monad) |
| `Gen.below n`, `Gen.range lo hi`, `Gen.bool`, `Gen.bv w` | numbers |
| `Gen.bvSmall w` | mostly small values, sometimes `0`/`max`/the sign bit, sometimes anything, so ties and edge cases actually happen |
| `Gen.elements xs`, `Gen.frequency [(w, g), …]` | choice |
| `Gen.list maxLen g`, `Gen.vector n g`, `Gen.sortedList maxLen g` | lists |
| `forAll g p (n := 200) (seed := 0)` | `p` holds on `n` samples, for `#guard` |
| `counterexample? g p` | the first failing sample, for `#eval` when a `#guard` fails |
| `samples g` | the samples themselves, e.g. to check a generator produces both outcomes |

The usual "run the code" helper lays the input out in memory, calls `Fn.callMem` and reads the result back:

```lean
def runIsSorted (xs : List (BitVec 32)) : Option Bool :=
  let cells := u32s xs
  match isSorted.callMem [.ptr .u32 ⟨0, 0⟩, .u32 xs.length]
      [(0, if cells.isEmpty then [.u32 0] else cells)] with
  | .ok (.bool b, _) => some b
  | _ => none

#guard forAll genList fun xs => runIsSorted xs == some (isSortedRef xs)
```

(A zero-length block isn't allowed, so an empty list gets one dummy cell that's never read.)

## The refinement theorem

The theorem says the return value *is* the reference's value, not that it satisfies some relation:

```lean
theorem isSorted_refines … (ha : array p (u32s xs) h) … :
    ∃ m', isSorted.Returns P [.ptr .u32 p, .u32 xs.length] m (.bool (isSortedRef xs)) m' ∧
      m'.heap = m.heap
```

For a function that writes through a pointer, say what ends up in memory in terms of the reference:

```lean
theorem parseU32_refines … :
    ∃ m' h', parseU32.Returns P [...] m (.bool (parseRef cs).isSome) m' ∧ … ∧
      (array p (u8s cs) ∗ array o [((parseRef cs).map nu32).getD w]) h'
```

## Examples

### `is_sorted`, written spec-first ([Examples/SpecFirst.lean](../Examples/SpecFirst.lean))

The reference is `xs.Pairwise (·.toNat ≤ ·.toNat)`: every element is `≤` every *later* one. The code only compares *neighbours*, so the proof does real work in showing the two agree.

- Tests of the reference: edge cases (empty, equal neighbours, unsigned order), sorting is the identity exactly on sorted lists, prefixes and suffixes of sorted lists are sorted, and the generator produces both outcomes.
- Code vs. reference: 200 random lists, half of them sorted. Changing `y < x` to `y <= x` in the code fails this `#guard`.
- Proof: `lc_auto` plus `lc_while` with the invariant "neighbours before `i` are in order". It leaves four goals, one per lemma: `adj_one` (entry), `adj_succ` (step), `sorted_of_adj` (exit: neighbours in order means `Pairwise`), `not_sorted_of_desc` (the early `return false`).

### `parse_u32` and `lower_bound`, retrofitted ([Examples/Refinement.lean](../Examples/Refinement.lean))

Their original specs are relational (`ParseOk`, "everything before `k` is `< x`"). Each now has a reference function and a refinement theorem, proved as a corollary of the original proof.

- **`parseRef`** is tested against Lean's `String.toNat?`. That found a real disagreement: `"1_000".toNat? = some 1000`, because Lean allows `_` as a digit separator, and C-style parsing doesn't. The oracle has to exclude `_`. A spec written by copying the "obvious" library function would have been wrong.
- **`lowerBoundRef xs x = (xs.takeWhile (· < x)).length`** is tested against `(xs.filter (· < x)).length` on sorted lists. A second `#guard` checks that the two *differ* on some unsorted list, so the precondition is not vacuous.
- **Executable preconditions.** `sorted_of_sortedRef` shows that `is_sorted`'s reference `SortedRef` implies the `Sorted` that `lower_bound`'s proof assumes. So `lowerBound_refines` takes the checkable `SortedRef xs`, and a caller can establish it at run time with the verified `is_sorted`.

## Tips

- **Make the generator hit the interesting cases.** Uniform random 32-bit values are almost never equal, so `Gen.bvSmall` and `Gen.sortedList` exist. Check with `samples` that both branches of the spec happen.
- **Test the spec against something written differently.** A property restating the definition proves nothing. Use a library function, a slower algorithm, or an algebraic law.
- **When an oracle disagrees, decide which is right and write it down.** The `_` case in `parse_u32` is now a `#guard` and a doc comment.
- **Keep the relational spec too, if you have it.** It's often easier to prove against, and the refinement theorem is a short corollary (see `lowerBound_refines`).
