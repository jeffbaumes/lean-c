import LC

/-!
# Printer stress tests

Each function exercises a place where C's rules differ from LC's: integer promotion of
narrow types, signed division and remainder, narrow negation and complement, casts, and
signed overflow. `lake exe lc difftest` runs them against the interpreter.
-/

open LC

namespace Tests.PrinterStress

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
-- A condition that is a bare variable or literal still needs C's parentheses: `if (t)`.
def condVar : Fn :=
  { name := "cond_var", params := [("a", .int .u32)], locals := [("t", .bool), ("r", .int .u32)],
    body := .block ["t" ::= v "a" <. .u32 10, "r" ::= .u32 0,
      .ite (v "t") ("r" ::= v "a") .skip, .while .ff .skip],
    ret := .int .u32, result := v "r" }

#guard match cTranslationUnit [condVar] with
  | .ok s => (s.splitOn "if (t) {").length == 2 && (s.splitOn "while (false) {").length == 2
  | .error _ => false

def all : List Fn :=
  [mul16, add8, sub8, shl8, neg8, not16, mulI16, addI32, divI32, modI32, negI64, ltI8,
   castU8, castI8, castI64, condVar]

#guard all.all Fn.typeCheck
#guard cKeywords.all (fun k => !cValidIdent k)

end Tests.PrinterStress
