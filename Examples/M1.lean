import LC

/-!
# Milestone 1 examples

Each program is a plain `Fn` value. For each one we check that it type-checks,
run it with `#eval`, and lock in its behaviour with `#guard`. A couple of runs
are turned into **theorems** about the semantics via `Fn.call_sound`: the
interpreter acts as a proof generator.
-/

open LC

namespace Examples.M1

/-! ## 1. Sum 1..n (the Milestone-2 proof target)

```c
uint64_t sum_to(uint32_t n) {
  uint32_t i = 0; uint64_t s = 0;
  while (i < n) { i = i + 1; s = s + (uint64_t)i; }
  return s;
}
```
-/
def sumTo : Fn where
  name   := "sum_to"
  params := [("n", .int .u32)]
  locals := [("i", .int .u32), ("s", .int .u64)]
  body   := .block [
    "i" ::= .u32 0,
    "s" ::= .u64 0,
    .while (v "i" <. v "n") (.block [
      "i" ::= v "i" + .u32 1,
      "s" ::= v "s" + .cast .u64 (v "i")
    ])
  ]
  ret    := .int .u64
  result := v "s"

#guard sumTo.typeCheck
#eval sumTo.call [.u32 10]                       -- ok 55u64
#guard sumTo.call [.u32 10] = .ok (.u64 55)
#guard sumTo.call [.u32 100000] (fuel := 1000000) = .ok (.u64 5000050000)  -- beyond 2³²: the u64 accumulator matters

/-- A theorem about the *semantics*, not the interpreter: `sum_to(10)` returns 55.
`decide` makes the kernel evaluate the interpreter; `call_sound` turns that into
an `Exec` derivation. No `native_decide`, so the compiler is not trusted. -/
theorem sumTo_10 : ∃ m', sumTo.Returns [.u32 10] [] (.u64 55) m' :=
  Fn.call_sound (fuel := 100) (by decide)

/-! ## 2. Euclid's GCD -/
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

theorem gcd_1071_462 : ∃ m', gcd.Returns [.u32 1071, .u32 462] [] (.u32 21) m' :=
  Fn.call_sound (fuel := 100) (by decide)

/-! ## 3. Popcount: shifts and masks on unsigned values -/
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

/-! ## 4. UB is *stuck*: signed overflow

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
def sub32u : Fn := { sub32 with params := [("a", .int .u32), ("b", .int .u32)], ret := .int .u32 }
#guard sub32u.call [.u32 0, .u32 1] = .ok (.u32 0xFFFFFFFF)

/-! ## 5. Other UB the semantics catches -/
def ubZoo (e : Expr) (t : IntTy) : Fn :=
  { name := "ub", params := [], locals := [], body := .skip, ret := .int t, result := e }

#guard (ubZoo (.u32 1 / .u32 0) .u32).call [] = .stuck                       -- division by zero
#guard (ubZoo (.i32 (-2147483648) / .i32 (-1)) .i32).call [] = .stuck         -- INT_MIN / -1
#guard (ubZoo (.i32 (-2147483648) % .i32 (-1)) .i32).call [] = .stuck         -- INT_MIN % -1 (C11 §6.5.5¶6)
#guard (ubZoo (Expr.u32 1 <<< Expr.u32 32) .u32).call [] = .stuck                     -- shift ≥ width
#guard (ubZoo (-(.i8 (-128))) .i8).call [] = .stuck                           -- -INT8_MIN
#guard (ubZoo (.cast .i8 (.u32 200)) .i8).call [] = .stuck                    -- impl-defined conversion
#guard (ubZoo (.cast .u8 (.i32 (-1))) .u8).call [] = .ok (.u8 255)            -- defined: mod 2⁸
#guard (ubZoo (.u16 0xFFFF * .u16 0xFFFF) .u16).call [] = .ok (.u16 1)        -- LC: wraps (printer must cast! see A3)

/-! ## 6. Short-circuit `&&` protects the right operand, as in C -/
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

/-! ## 7. Reading an uninitialised local is stuck -/
def uninit : Fn where
  name := "uninit"; params := []; locals := [("x", .int .u32)]
  body := .skip; ret := .int .u32; result := v "x"

#guard uninit.typeCheck            -- it type-checks…
#guard uninit.call [] = .stuck     -- …but has no meaning (C11 §6.3.2.1¶2 / J.2)

/-! ## 8. Divergence is neither ok nor stuck -/
def spin : Fn where
  name := "spin"; params := []; locals := []
  body := .while .tt .skip; ret := .bool; result := .tt

#guard spin.call [] (fuel := 1000) = .outOfFuel

/-! ## 9. The type checker rejects mixed widths -/
def bad : Fn where
  name := "bad"; params := [("a", .int .u8), ("b", .int .u32)]; locals := []
  body := .skip; ret := .int .u32; result := v "a" + v "b"

#guard !bad.typeCheck
#guard bad.call [.u8 1, .u32 2] = .stuck   -- the dynamic semantics agrees

end Examples.M1
