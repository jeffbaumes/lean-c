import LC

/-!
# Semantics tests: what is UB, what isn't

Each `#guard` pins down one C11 rule in LC's semantics. A `stuck` result means the
semantics treats the program as undefined; `run_stuck_sound` makes that a fact about
every execution, not just the interpreter.
-/

open LC

namespace Tests.Semantics

/-! ## Undefined (or implementation-defined) operations are stuck -/
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


/-! ## Reading an uninitialised local is stuck -/
def uninit : Fn where
  name := "uninit"; params := []; locals := [("x", .int .u32)]
  body := .skip; ret := .int .u32; result := v "x"

#guard uninit.typeCheck            -- it type-checks…
#guard uninit.call [] = .stuck     -- …but has no meaning (C11 §6.3.2.1¶2 / J.2)

/-! ## Divergence is neither ok nor stuck -/
def spin : Fn where
  name := "spin"; params := []; locals := []
  body := .while .tt .skip; ret := .bool; result := .tt

#guard spin.call [] (fuel := 1000) = .outOfFuel

/-! ## The type checker rejects mixed widths -/
def bad : Fn where
  name := "bad"; params := [("a", .int .u8), ("b", .int .u32)]; locals := []
  body := .skip; ret := .int .u32; result := v "a" + v "b"

#guard !bad.typeCheck
#guard bad.call [.u8 1, .u32 2] = .stuck   -- the dynamic semantics agrees


end Tests.Semantics
