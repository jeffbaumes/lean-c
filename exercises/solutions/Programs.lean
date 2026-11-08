-- Solutions to exercises/core/Programs.lean.  Run: lake env lean exercises/solutions/Programs.lean
import LC
import Examples.Search
import Examples.ParseU32
open LC Examples.Search Examples.ParseU32

/-! ## Prog.1
The `mid` step fails: it needs `lo + (hi - lo) / 2` to equal the `BitVec` the code computes.
With `(lo + hi) / 2`, the sum is computed mod 2³², so the proof would need `lo + hi < 2³²`.
That holds only if `n ≤ 2³¹`. For arrays longer than that the sum wraps (defined
behaviour, so no sanitizer complains), `mid` lands below `lo`, and the search goes wrong. -/

/-! ## Prog.2 -/
def allDigits : Fn where
  name := "all_digits"; params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("c", .int .u8), ("ok", .bool)]
  body := .block [
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "c" (v "p") (v "i"),
      .call (some "ok") "is_digit" [v "c"],
      .ite (!. (v "ok")) (.ret .ff) .skip,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret := .bool; result := .tt

def prog2 : Program := [isDigit, allDigits]
#guard allDigits.typeCheck prog2

def runAll (s : String) : Result (Val × Mem) :=
  let bytes := s.toList.map fun c => Val.u8 c.toNat
  allDigits.callMem [.ptr .u8 ⟨0, 0⟩, .u32 bytes.length] [(0, bytes ++ [Val.u8 0])] (P := prog2)

def resultOf : Result (Val × Mem) → Option Val
  | .ok (v, _) => some v
  | _ => none

#guard resultOf (runAll "123") = some (.bool true)
#guard resultOf (runAll "12x") = some (.bool false)
#guard resultOf (runAll "") = some (.bool true)

/-! ## Prog.4
`hbody` is `isDigit_spec P cs[i]`, proved once about `is_digit`'s body. The call rule looks the
callee up *by name* in the program (`Exec.call` uses `P.find? f`). The hypothesis says the name
"is_digit" really refers to the verified function. Without it, `P` could contain a different
function called `is_digit` (say, one that always returns true), and the theorem would be false. -/
