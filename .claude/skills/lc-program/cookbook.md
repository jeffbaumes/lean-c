# LC proof cookbook

Patterns for the shapes the basic skeleton in [SKILL.md](SKILL.md) doesn't cover. Each points at a file in the repo that does it; copy from there. Paths are from the repo root.

## Early `return` (or the result comes from `.ret`)

Use `swpo` (one postcondition per outcome) and `Fn.finish`, which turns `return v` or falling off the end into the call's value. From `isSorted_refines` in `Examples/SpecFirst.lean`:

```lean
  suffices hbody : swpo P isSorted.body (fun o st h' => ∃ v, isSorted.finish o st = some v ∧
      (v = .bool (isSortedRef xs) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swpo
      (post := fun v h' => v = .bool (isSortedRef xs) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (sortedInv p xs h) (counterVariant xs.length) [sortedInv, counterVariant]
  · exact not_sorted_of_desc ‹_› ‹_› ‹_›     -- the `return false` inside the loop
  · ...
```

Each `return` leaves a goal that is the postcondition at that point; prove "why returning here is right" as a lemma (`not_sorted_of_desc`, `not_ok_of_overflow`). If the theorem's conclusion is already `∃ v m' h', f.Returns … ∧ h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ post`, skip the `suffices`: `refine Fn.returns_of_swpo hinit ?_ d hm` (see `parseU32_correct` in `Examples/Auto.lean`).

`break` needs nothing special: `lc_while` makes the `break` branch prove the loop's exit condition (`findFirst_correct`).

## A postcondition with a disjunction or an existential

Name it with `let post : Val → HProp := fun v h' => …` and pass it to `Fn.returns_of_swp(o)` implicitly; `lc_auto` picks existential witnesses from store equations (`find_first`, `lower_bound` in `Examples/Auto.lean`). For "succeeds iff", state both sides: `(Ok cs ∧ v = .bool true ∧ …) ∨ (¬ Ok cs ∧ v = .bool false ∧ h' = h)`.

## Writing through pointers

The precondition is a `∗`-tree of `array`s, and the theorem returns the new heap `h'` (`Examples/Copy.lean`, `copy_correct` in `Examples/Auto.lean`):

```lean
    (hpre : (array dst (u8s ds) ∗ array src (u8s ss)) h) (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m' h', copy.Returns P [...] m .unit m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧ (array dst (u8s ss) ∗ array src (u8s ss)) h'
```

The invariant carries the same `∗`-tree with the partly written contents, `array dst (u8s (ss.take i ++ ds.drop i)) ∗ array src (u8s ss)`. `lc_auto` finds the cell for loads and rewrites the array after stores; it leaves the list identity (`copy_step'`), which `List.ext_getElem?` plus `simp only [List.getElem?_set, List.getElem?_append, …]` and `grind` usually closes.

Limits: the final `∗` match pairs parts **by position**, so keep the same tree shape (same order) in pre, invariant and post. No sub-buffers (`p + k`): pass a separate pointer and length.

By hand, the lemmas are `star_get_left/right` (read a cell through `∗`) and `star_update_left/right` (write one), with `array_get`/`array_update` for the array part (`Examples/Copy.lean`, `Examples/RingBuffer.lean`). For nested trees, compose: `star_get_left hsep fun _ ha => star_get_right ha fun _ ha' => array_get ha' hk`.

## Calling a verified function

1. Prove the callee's **body** spec (not `Returns`) in this shape, with the arguments as a concrete store (`isDigit_spec` in `Examples/ParseU32.lean`):

   ```lean
   theorem isDigit_spec (P : Program) (c : BitVec 8) :
       swpo P isDigit.body (fun o st h' => ∃ v, isDigit.finish o st = some v ∧
         v = .bool (decide (IsDigit c)) ∧ h' = Heap.empty) [("c", .int .u8 c)] Heap.empty
   theorem isDigit_init (c : BitVec 8) : isDigit.initStore [.int .u8 c] = some [("c", .int .u8 c)]
   ```

2. Put both functions in a `def prog : Program := [callee, caller]`, and type-check with `caller.typeCheck prog`.
3. The caller's theorem takes `(hP : P.find? "is_digit" = some isDigit)`, so it holds in every program where the name means the verified function.
4. At the call: `lc_call hP (isDigit_spec P _) (isDigit_init _) [extras]`. The `_`s are found by unification with the argument values. With a loop around the call, `lc_while` first, then `lc_call` with the same extras.

Callees that read or write the caller's memory need the general rule `swpo_call` (`LC/Logic/Sep.lean`): split the caller's heap into `h₁.union h₂`, give the callee `h₁`, and the frame `h₂` comes back untouched. `lc_call` doesn't do this yet; apply `swpo_call` by hand, then go back to `lc_auto`.

## A variant other than `n - i`

Write it as a function of the store (`lbVar` in `Examples/Search.lean`, for binary search):

```lean
def lbVar : Store → Heap → Nat := fun st _ =>
  match st.get "lo", st.get "hi" with
  | some (.int _ a), some (.int _ b) => b.toNat - a.toNat
  | _, _ => 0
```

and pass it to `lc_while` and in the extras.

## Arithmetic

- `lc_auto` rewrites in-range `BitVec.ofNat` arithmetic to `Nat` (`bv_sub`, `bv_udiv`, `bv_mul` in `LC/Spec.lean`) when `omega` can show the range from hypotheses. A leftover `% 2 ^ 32` means it couldn't: add the bound to the invariant.
- Overflow checks before the operation: `acc > (UINT32_MAX - d) / 10` is exactly "`acc * 10 + d` doesn't fit", and after rewriting it's linear with literal divisors, so `omega` proves it (`parse_u32`).
- Midpoints: `lo + (hi - lo) / 2`, never `(lo + hi) / 2`.
- New general rewrite lemmas: tag them `attribute [lc_simp] myLemma` and `lc_auto` uses them everywhere.

## Leftover goals

They have inaccessible names (`a✝`, `left✝²`). Don't fight that: write a lemma whose hypotheses are the facts the goal needs, and apply it with `‹_›` for each (Lean finds them by type) or `(by omega)`:

```lean
  · exact digits_succ ‹_› ‹_› ‹_› ‹_›
  · exact sorted_below hs (by omega) ‹_›
  · simp [‹¬_›]
```

Inspect them first with `all_goals trace_state`. If you need names, `rename_i a b c` (names the last three inaccessible hypotheses, in order) or `next x hx => …`.

Typical lemma shapes:
- **succ**: the reference on `xs.take (i + 1)` in terms of `xs.take i` and `xs[i]` (`countRef_take_succ`, `decVal_take_succ`, `psum_succ`). Proof: `List.take_succ_eq_append_getElem hi`, then `List.filter_append`/`List.foldl_append`/`List.length_append`, `simp`.
- **exit**: at `i = xs.length`, `xs.take i = xs` (`List.take_length`), or "all prefix facts" gives the full spec (`sorted_of_adj`).
- **∀ j < i + 1** from `∀ j < i` plus the new element: `rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl` (`digits_succ`).
- **`xs[j]?` to `xs[j]`**: `List.getElem?_eq_getElem (by omega)`.

## Proofs by hand (when `lc_auto` isn't enough)

The rules are `swp_seq`, `swp_assign'`, `swp_load'`, `swp_store'`, `swp_ite`, `swp_while`, and the `swpo_` versions (`LC/Logic/Sep.lean`). Unfold first: `simp only [f, Stmt.block]`. Each primed rule asks for an existential: the value, the proof it's what the expression evaluates to, then the rest.

- **Both branches of an `if` continue with the same code** (`Examples/RingBuffer.lean`, `rbPush_correct`): don't use bullets. Prove each branch up to the join, then `rotate_left` to bring the other branch's goal forward, and finish both tails at once with `all_goals`.
- **A custom heap predicate** (the ring buffer's `rb`) isn't a `∗`-tree of arrays, so `lc_auto` doesn't understand it. Destructure it at the start (`obtain ⟨cells, head, …, hsep⟩ := hrb`) to expose the `∗`-tree, and rebuild it at the end.

## Refinement as a corollary

If a relational spec is easier to prove (`lowerBound_correct`: "everything before `k` is `< x`, everything from `k` on is `≥ x`"), prove that, then derive refinement in a few lines with a lemma that the relation determines the reference's value (`lowerBound_refines` in `Examples/Refinement.lean`). Give preconditions an executable form too (`SortedRef`), so callers can check them at run time with another verified function.
