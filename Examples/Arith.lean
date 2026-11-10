import LC

/-!
# Small arithmetic functions

GCD, popcount, signed/unsigned subtraction and a short-circuit guard, each checked
against the interpreter. These are also part of the differential test suite.
-/

open LC

namespace Examples.Arith

/-! ## Euclid's GCD -/
def gcd : Fn where
  name   := "gcd"
  params := [("a", .int .u32), ("b", .int .u32)]
  locals := [("t", .int .u32)]
  body   := .while (v "b" !=. .u32 0) (.block [
      "t" ::= v "b",
      "b" ::= v "a" % v "b",
      "a" ::= v "t"
    ])
  ret    := .int .u32
  result := v "a"

#guard gcd.typeCheck
#guard gcd.call [.u32 1071, .u32 462] = .ok (.u32 21)
#guard gcd.call [.u32 0, .u32 0] = .ok (.u32 0)

theorem gcd_1071_462 : ∃ m', gcd.Returns [] [.u32 1071, .u32 462] [] (.u32 21) m' :=
  Fn.call_sound (fuel := 100) (by decide)

/-! ## Popcount: shifts and masks on unsigned values -/
def popcount : Fn where
  name   := "popcount"
  params := [("x", .int .u32)]
  locals := [("c", .int .u32)]
  body   := .block [
    "c" ::= .u32 0,
    .while (v "x" !=. .u32 0) (.block [
      "c" ::= v "c" + (v "x" &&& Expr.u32 1),
      "x" ::= v "x" >>> Expr.u32 1
    ])
  ]
  ret    := .int .u32
  result := v "c"

#guard popcount.typeCheck
#guard popcount.call [.u32 0xFFFFFFFF] = .ok (.u32 32)
#guard popcount.call [.u32 0b1011] = .ok (.u32 3)

/-! ## UB is *stuck*: signed overflow

`a - b` on `int32_t` is fine until the mathematical result leaves
[−2³¹, 2³¹−1], and then it is UB in C. Our interpreter reports `stuck`, and
`run_stuck_sound` guarantees that no execution exists at all. -/
def sub32 : Fn where
  name   := "sub32"
  params := [("a", .int .i32), ("b", .int .i32)]
  locals := []
  body   := .skip
  ret    := .int .i32
  result := v "a" - v "b"

#guard sub32.call [.i32 5, .i32 7] = .ok (.i32 (-2))
#guard sub32.call [.i32 (-2147483648), .i32 1] = .stuck      -- INT32_MIN - 1: UB
#eval sub32.call [.i32 (-2147483648), .i32 1]

/-- …and the same program at `uint32_t` wraps, as C requires. -/
def sub32u : Fn := { sub32 with name := "sub32u", params := [("a", .int .u32), ("b", .int .u32)], ret := .int .u32 }
#guard sub32u.call [.u32 0, .u32 1] = .ok (.u32 0xFFFFFFFF)


/-! ## Short-circuit `&&` protects the right operand, as in C -/
def safeDivGt1 : Fn where
  name   := "safe_div_gt1"
  params := [("n", .int .u32), ("d", .int .u32)]
  locals := []
  body   := .skip
  ret    := .bool
  result := v "d" !=. .u32 0 &&. v "n" / v "d" >. .u32 1

#guard safeDivGt1.typeCheck
#guard safeDivGt1.call [.u32 10, .u32 0] = .ok (.bool false)   -- n/d never evaluated
#guard safeDivGt1.call [.u32 10, .u32 3] = .ok (.bool true)


end Examples.Arith

#print axioms Examples.Arith.gcd_1071_462
