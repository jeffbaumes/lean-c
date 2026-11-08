# Calls, `break`/`return`, and verified real programs

LC can now verify small *libraries*, not just single functions. Functions call each other, specs compose, and loops can exit early. Everything is proved with no `sorry` and no `native_decide`, and differentially tested as C.

## What was added to the language

| | Syntax | C | Semantics |
|---|---|---|---|
| break | `Stmt.brk` | `break;` | the statement finishes with outcome `brk`; the innermost `while` ends normally |
| return | `Stmt.ret e` | `return e;` | outcome `ret v`; unwinds to the call |
| call | `Stmt.call (some x) f args` | `x = f(args);` | runs `f`'s body in a fresh store on the *shared* memory, then assigns the result |

**Outcomes.**
- `Exec P σ s o σ'` now records *how* `s` finished: `o ∈ {normal, brk, ret v}`.
- `seq` and `while` propagate abrupt outcomes the way C does. This is CompCert Clight's `outcome` treatment.
- `Fn.finish` turns a body's outcome into the call's value: `return v` gives `v`, and falling off the end evaluates `result`.

**Programs.** `Exec` takes a `Program` (a list of `Fn`), and `call` looks the callee up *by name*. Arguments are pure expressions, so C's unspecified argument evaluation order can't matter.

**What was re-proved.** The interpreter (`run`) and all its theorems now handle outcomes and calls: soundness, determinism (now over outcomes too), stuck-soundness, and type preservation. Every existing proof survived. `sum_to`, array sum, `copy` and the ring buffer needed only the extra program parameter `P` in their statements. They now hold *in every program*, since they call nothing.

**Type checking.**
- `break` is allowed only inside a loop.
- `return e` must match the function's return type.
- A call must match the callee's signature in the program.
- `Fn.typeCheck f P` checks `f` against program `P`.

## The program logic for it ([LC/Logic/Sep.lean](../LC/Logic/Sep.lean))

`swpo P s Q` is the local weakest precondition with **one postcondition per outcome** (`Q .normal`, `Q .brk`, `Q (.ret v)`). The old `swp` is the normal-only special case, and `swpo_of_swp` embeds it, so straight-line reasoning is unchanged.

| Rule | Meaning |
|---|---|
| `swpo_seq` | if `s₁` finishes normally, continue with `s₂`; otherwise its outcome is the answer |
| `swpo_brk`, `swpo_ret` | `break` / `return e` establish `Q .brk` / `Q (.ret v)` |
| `swpo_while` | invariant + variant; the body's `break` must establish the loop's normal postcondition, and its `return` must establish the loop's `return` postcondition |
| **`swpo_call`** | **the modular call rule.** The caller owns `h₁ ⊎ h₂`; the callee gets `h₁`. Given the callee's body proof (an instance of the callee's own spec theorem), the call returns `v` with the callee's postcondition about `h₁'`, and `h₂` is untouched. This is the frame rule at a function boundary |
| `swpo_call_pure` | the same for callees that own no memory |
| `Fn.returns_of_swpo` | from a body proof (with `return`s) to `f.Returns P args m v m'` |

## The programs

### `find_first(a, n, x)` ([Examples/Search.lean](../Examples/Search.lean)): linear search with `break`

**Spec (`findFirst_correct`):** returns `k ≤ n` such that no element before `k` is `x`, and `a[k] = x` if `k < n`.

**Proof:** the `break` branch proves the *loop's* normal postcondition directly, the found-it case. About 55 lines.

### `lower_bound(a, n, x)`: binary search

```c
uint32_t lower_bound(uint32_t *a, uint32_t n, uint32_t x) {
  ...
  lo = 0u;
  hi = n;
  while (lo < hi) {
    mid = (lo + ((hi - lo) / 2u));
    t = a[mid];
    if (t < x) {
      lo = (mid + 1u);
    } else {
      hi = mid;
    }
  }
  return lo;
}
```

**Spec (`lowerBound_correct`):** for any **sorted** array of length < 2³², the result `k` splits it: everything before `k` is `< x`, and everything from `k` on is `≥ x`. Memory is unchanged.

**Midpoint:** `lo + (hi - lo) / 2`, not `(lo + hi) / 2`, which wraps for `n > 2³¹`. This is Bloch's 2006 bug, and exercise Prog.1. The proof needs `bv_sub` and `bv_udiv` to see that the bit-vector arithmetic is exact. About 75 lines.

### `is_digit(c)` and `parse_u32(p, n, out)` ([Examples/ParseU32.lean](../Examples/ParseU32.lean)): a parser that calls a verified helper

```c
bool parse_u32(uint8_t *p, uint32_t n, uint32_t *out) {
  ...
  if (n == 0u) {
    return false;
  }
  i = 0u;
  acc = 0u;
  while (i < n) {
    c = p[i];
    ok = is_digit(c);
    if (!ok) {
      return false;
    }
    d = (((uint32_t)c) - 48u);
    if (((4294967295u - d) / 10u) < acc) {
      return false;
    }
    acc = ((acc * 10u) + d);
    i = (i + 1u);
  }
  out[0u] = acc;
  return true;
}
```

**Spec (`parseU32_correct`):**
- It returns `true` and writes `decVal cs` to `out[0]` **if and only if** `cs` is non-empty, all digits, and its value is < 2³².
- Otherwise it returns `false` and memory is unchanged.
- It holds in any program in which `"is_digit"` names the verified `is_digit`.

**What the proof shows:**
- **Modularity.** The call site uses `isDigit_spec`, never `is_digit`'s code (`swpo_call_pure`).
- **Early return.** Each `return false` proves the "not `ParseOk`" half of the spec right there. The non-digit case uses the digit found; the overflow case uses `decVal_take_le`: if a prefix overflows, so does the whole string.
- **Overflow before it happens.** `acc > (UINT32_MAX - d) / 10` is exactly `acc * 10 + d > UINT32_MAX`. After `bv_sub`/`bv_udiv`/`bv_mul`, `omega` proves that, because it's linear with literal divisors.

It's about 120 lines.

## Testing

`lake exe lc difftest` now runs functions inside their program; for `parse_u32`, `is_digit` is printed in the same translation unit. Byte buffers are sometimes filled with ASCII digits, so the parser gets past its first byte. Results (`nice -n 19 lake exe lc difftest 100 5 <fn>`):

| function | ok | stuck (sanitizer-flagged) | result |
|---|---|---|---|
| `find_first` | 57 | 43 (20/20) | PASS |
| `lower_bound` | 50 | 50 (17/20) | PASS |
| `is_digit` | 100 | 0 | PASS |
| `parse_u32` | 84 | 16 (16/16) | PASS |

The three unflagged `lower_bound` cases are wild reads: `n = 149` on a 7-element array makes the first `mid` read 268 bytes past the end, beyond ASan's redzone. The interpreter calls it UB, and the proofs rule it out.

## Using the C

`lake exe lc emit generated/lc_examples` writes [generated/lc_examples.h](../generated/lc_examples.h) and [generated/lc_examples.c](../generated/lc_examples.c):
- The `.h` has an include guard, `<stdint.h>`/`<stdbool.h>`, and one prototype per function.
- The `.c` includes it and needs only freestanding headers. It compiles with `-std=c11 -ffreestanding -Wall -Wextra -Werror -pedantic`.

Drop both files into a C project.

## Still missing

- **Structs** (`rb->head`).
- **Sub-buffers** (`p + k` as an argument).
- **Fixed-size local arrays.**
- **Proof automation** (`sep_simp`). The new proofs are 55–120 lines, and about a third of that is heap and store bookkeeping.
- **The printer is still trusted** (tested, not proved).

## Exercises

[exercises/core/Programs.lean](../exercises/core/Programs.lean):

- **Prog.1:** the midpoint bug.
- **Prog.2:** write `all_digits` reusing `is_digit`.
- **Prog.3 (stretch):** prove it.
- **Prog.4:** why the theorem needs `P.find? "is_digit" = some isDigit`.
