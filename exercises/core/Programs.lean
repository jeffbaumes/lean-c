/-
Exercises on calls, `break`/`return`, and the verified programs.
Run:  lake env lean exercises/core/Programs.lean      (after `lake build`)

Read docs/programs.md, Examples/Search.lean and Examples/ParseU32.lean first.
Solutions: exercises/solutions/Programs.lean.
-/
import LC
import Examples.Search
import Examples.ParseU32
open LC Examples.Search Examples.ParseU32

/-! ## Prog.1 (✍️ 10 min): the midpoint
Change `lower_bound`'s midpoint to `(lo + hi) / 2`. The `#guard`s still pass. Which step of
`lowerBound_correct` breaks, and for what array sizes is the new code actually wrong? -/

/-! ## Prog.2 (🔧 15 min): reuse a verified helper
Write `all_digits(p, n) → bool`: true iff every byte of `p[0..n)` is a digit. Call `is_digit`
from it, and return early on the first non-digit. Put both functions in a program (like `prog`
in Examples/ParseU32.lean), then test with `callMem … (P := …)` on "123", "12x" and "". -/
def allDigits : Fn where
  name := "all_digits"; params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("c", .int .u8), ("ok", .bool)]
  body := .skip   -- TODO
  ret := .bool; result := .tt

/-! ## Prog.3 (🔧 stretch, 2 × 15 min): prove `all_digits`
State and prove: `all_digits` returns `true` iff `∀ c ∈ cs, IsDigit c`, and the heap is unchanged.
Model the loop on `parseU32_correct`'s, and the call on its use of `swpo_call_pure` with
`isDigit_spec`. No solution file yet. -/

/-! ## Prog.4 (✍️ 5 min): what the call rule assumes
`swpo_call` takes the callee's body proof as `hbody`. Where does that come from in
`parseU32_correct`, and why does the theorem need the hypothesis
`P.find? "is_digit" = some isDigit`? What would go wrong without it? -/
