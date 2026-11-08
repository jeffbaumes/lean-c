import LC
import Examples.M3

/-!
# Milestone 4: programs that stress the C printer

Each function exercises a place where C's rules differ from LC's: integer promotion
of narrow types, signed division and remainder, narrow negation and complement,
casts, and signed overflow. The differential tester (`lake exe lc difftest`) runs
all of them, plus the M1–M3 examples, against the interpreter.
-/

open LC

namespace Examples.M4

/-- A one-expression function `name(a : t, b : t) → r := e`. -/
def binFn (name : String) (t r : IntTy) (e : Expr) : Fn :=
  { name, params := [("a", .int t), ("b", .int t)], locals := [], body := .skip,
    ret := .int r, result := e }

def unFn (name : String) (t r : IntTy) (e : Expr) : Fn :=
  { name, params := [("a", .int t)], locals := [], body := .skip, ret := .int r, result := e }

-- Unsigned narrow types: C promotes to *signed* int. Naive `a * b` is UB at 0xFFFF².
def mul16 := binFn "mul16" .u16 .u16 (v "a" * v "b")
def add8  := binFn "add8"  .u8  .u8  (v "a" + v "b")
def sub8  := binFn "sub8"  .u8  .u8  (v "a" - v "b")       -- wraps below zero
def shl8  := binFn "shl8"  .u8  .u8  (v "a" <<< v "b")     -- amount must be < 8
def neg8  := unFn  "neg8"  .u8  .u8  (-(v "a"))
def not16 := unFn  "not16" .u16 .u16 (~~~(v "a"))
-- Signed: overflow is stuck in LC, UB in C, so the tester must never run it.
def mulI16 := binFn "mul_i16" .i16 .i16 (v "a" * v "b")
def addI32 := binFn "add_i32" .i32 .i32 (v "a" + v "b")
def divI32 := binFn "div_i32" .i32 .i32 (v "a" / v "b")    -- truncates toward zero
def modI32 := binFn "mod_i32" .i32 .i32 (v "a" % v "b")    -- sign follows the dividend
def negI64 := unFn  "neg_i64" .i64 .i64 (-(v "a"))
def ltI8 : Fn := { binFn "lt_i8" .i8 .i8 (.u32 0) with ret := .bool, result := v "a" <. v "b" }
-- Casts: to unsigned wraps; to signed must be representable.
def castU8 := unFn "cast_u8" .i32 .u8 (.cast .u8 (v "a"))
def castI8 := unFn "cast_i8" .u32 .i8 (.cast .i8 (v "a"))
def castI64 := unFn "cast_i64" .u32 .i64 (.cast .i64 (v "a") * .i64 (-1))

/-- FNV-1a, 32-bit, over a byte buffer: a real function with wrapping multiply. -/
def fnv1a : Fn where
  name   := "fnv1a"
  params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("c", .int .u8), ("h", .int .u32)]
  body   := .block [
    "h" ::= .u32 2166136261,
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "c" (v "p") (v "i"),
      "h" ::= (v "h" ^^^ .cast .u32 (v "c")) * .u32 16777619,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u32
  result := v "h"

-- Known-answer test: FNV-1a("a") = 0xe40c292c.
#guard fnv1a.callMem [.ptr .u8 ⟨0, 0⟩, .u32 1] [(0, [.u8 97])] = .ok (.u32 0xe40c292c, [(0, [.u8 97])])

def stress : List Fn :=
  [mul16, add8, sub8, shl8, neg8, not16, mulI16, addI32, divI32, modI32, negI64, ltI8,
   castU8, castI8, castI64, fnv1a]

/-- Everything the differential tester runs. -/
def all : List Fn :=
  [Examples.M1.sumTo, Examples.M1.gcd, Examples.M1.popcount, Examples.M1.sub32,
   Examples.M1.sub32u, Examples.M1.safeDivGt1, Examples.M3.arraySum, Examples.M3.copy] ++ stress

#guard all.all Fn.typeCheck
#guard (cTranslationUnit all).isOk

end Examples.M4
