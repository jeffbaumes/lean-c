import LC.Typing

/-!
# The C printer (Milestone 4)

`Fn.toC : Fn → Except String String` prints an LC function as C11 that depends only
on the freestanding headers `<stdint.h>`, `<stdbool.h>` and `<limits.h>`.

**This file is in the trusted computing base.** Nothing here is proved yet (that's M6).
The differential tester (`Tools/DiffTest.lean`) is what checks it. So the rules
below are written to be *obviously* right, not clever:

1. **Everything is parenthesised.** No reliance on C precedence.
2. **Every expression is printed at its LC type**, which comes from the type checker,
   so a function must type-check before it can be printed.
3. **Integer promotions** (C11 §6.3.1.1). In C, `uint8_t`/`uint16_t`/`int8_t`/`int16_t`
   operands are promoted to `int` before arithmetic. For unsigned narrow types that
   makes `0xFFFF * 0xFFFF` *signed* overflow, which is UB (assignment A3, case 2). LC's
   semantics is "compute in the narrow type, wrap". So the printer computes in
   `uint32_t` and casts back: `((uint16_t)((uint32_t)a * (uint32_t)b))`. That is
   defined C with exactly LC's meaning.
   For signed narrow types the promoted computation is exact, and LC's semantics
   guarantees (by getting stuck otherwise) that the result fits, so we cast back.
4. **32-bit `int` is assumed** and checked with a `_Static_assert`. If `int` were 64 bits,
   `uint32_t` operands would promote to signed `int`, and the rule in (3) would need to
   use `uint64_t`. That assumption belongs in the TCB, and the assert makes it explicit.
5. **Names are printed verbatim** but must be valid, non-reserved C identifiers. The
   printer refuses anything else rather than mangling it, so the output stays readable
   and no renaming scheme needs to be proved injective.
-/

namespace LC

def IntTy.cName (t : IntTy) : String :=
  s!"{if t.signed then "int" else "uint"}{t.bits}_t"

def Ty.cName : Ty → String
  | .int t => IntTy.cName t
  | .bool => "bool"
  | .ptr t => IntTy.cName t ++ " *"
  | .unit => "void"

/-- `T x`, or `T *x` for pointers. -/
def cDecl (t : Ty) (x : String) : String :=
  match t with
  | .ptr t => s!"{IntTy.cName t} *{x}"
  | t => s!"{Ty.cName t} {x}"

/-- Types narrower than `int`, which C promotes before arithmetic. -/
def IntTy.narrow (t : IntTy) : Bool := t.bits < 32

def cKeywords : List String :=
  ["auto", "break", "case", "char", "const", "continue", "default", "do", "double", "else",
   "enum", "extern", "float", "for", "goto", "if", "inline", "int", "long", "register",
   "restrict", "return", "short", "signed", "sizeof", "static", "struct", "switch", "typedef",
   "union", "unsigned", "void", "volatile", "while", "_Alignas", "_Alignof", "_Atomic", "_Bool",
   "_Complex", "_Generic", "_Imaginary", "_Noreturn", "_Static_assert", "_Thread_local",
   "bool", "true", "false", "main"]

/-- A valid C identifier that is not a keyword and not reserved (C11 §7.1.3:
names starting with `_` followed by an uppercase letter or a second `_`). -/
def cValidIdent (x : String) : Bool :=
  match x.toList with
  | [] => false
  | c :: cs =>
    (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_') &&
    !cKeywords.contains x && !(c == '_' && (cs.head?.map (fun d => d.isUpper || d == '_')).getD false)

def cIdent (x : String) : Except String String :=
  if cValidIdent x then .ok x else .error s!"not a valid, non-reserved C identifier: {x}"

/-- An integer literal of type `t`, written so the C literal itself is in range. -/
def cIntLit (t : IntTy) (bv : BitVec t.bits) : String :=
  let ty := IntTy.cName t
  if t.signed then
    let z := bv.toInt
    if z = t.min then s!"INT{t.bits}_MIN"
    else if t.bits = 64 then s!"INT64_C({z})"
    else if t.bits = 32 then (if z < 0 then s!"({z})" else s!"{z}")   -- `int` is int32_t (asserted)
    else s!"(({ty}){z})"
  else
    if t.bits = 64 then s!"UINT64_C({bv.toNat})"
    else if t.bits = 32 then s!"{bv.toNat}u"                       -- `unsigned` is uint32_t
    else s!"(({ty}){bv.toNat}u)"

def cValLit : Val → Except String String
  | .int t bv => .ok (cIntLit t bv)
  | .bool b => .ok (if b then "true" else "false")
  | .ptr _ _ => .error "pointer literals cannot be printed"
  | .unit => .error "unit is not an expression in C"

def cBinSym : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .band => "&" | .bor => "|" | .bxor => "^" | .shl => "<<" | .shr => ">>"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<="
  | .land => "&&" | .lor => "||"

/-- Does this operator's *result* have the operand's integer type? (vs. `bool`) -/
def BinOp.arith : BinOp → Bool
  | .add | .sub | .mul | .div | .mod | .band | .bor | .bxor | .shl | .shr => true
  | _ => false

def Expr.toC (Γ : TyEnv) : Expr → Except String String
  | .lit v => cValLit v
  | .var x => cIdent x
  | .unop op e => do
    let s ← e.toC Γ
    match op, e.typeOf Γ with
    | .lnot, _ => return s!"(!{s})"
    | .neg, some (.int t) | .bnot, some (.int t) =>
      let sym := if op == .neg then "-" else "~"
      if t.narrow && !t.signed then
        -- compute in uint32_t (wraps), truncate back: LC's meaning
        return s!"(({IntTy.cName t})({sym}(uint32_t){s}))"
      else if t.narrow then
        return s!"(({IntTy.cName t})({sym}{s}))"
      else return s!"({sym}{s})"
    | _, _ => throw "ill-typed unary operator"
  | .binop op a b => do
    let sa ← a.toC Γ
    let sb ← b.toC Γ
    let sym := cBinSym op
    match a.typeOf Γ with
    | some (.int t) =>
      if op.arith && t.narrow then
        if t.signed then
          -- promoted to int: exact for 8/16-bit operands; LC guarantees the result fits
          return s!"(({IntTy.cName t})({sa} {sym} {sb}))"
        else
          return s!"(({IntTy.cName t})((uint32_t){sa} {sym} (uint32_t){sb}))"
      else return s!"({sa} {sym} {sb})"
    | some _ => return s!"({sa} {sym} {sb})"
    | none => throw "ill-typed binary operator"
  | .cast t e => do
    let s ← e.toC Γ
    return s!"(({IntTy.cName t}){s})"

def cIndent (n : Nat) : String := "".pushn ' ' (2 * n)

def Stmt.toC (Γ : TyEnv) (d : Nat) : Stmt → Except String String
  | .skip => return ""
  | .assign x e => return s!"{cIndent d}{← cIdent x} = {← e.toC Γ};\n"
  | .seq s₁ s₂ => return (← s₁.toC Γ d) ++ (← s₂.toC Γ d)
  | .ite c s₁ s₂ => do
    let e ← s₂.toC Γ (d + 1)
    let els := if e.isEmpty then "" else s!" else \{\n{e}{cIndent d}}"
    return s!"{cIndent d}if {← c.toC Γ} \{\n{← s₁.toC Γ (d + 1)}{cIndent d}}{els}\n"
  | .while c b => return s!"{cIndent d}while {← c.toC Γ} \{\n{← b.toC Γ (d + 1)}{cIndent d}}\n"
  | .load x p i => return s!"{cIndent d}{← cIdent x} = {← p.toC Γ}[{← i.toC Γ}];\n"
  | .store p i e => return s!"{cIndent d}{← p.toC Γ}[{← i.toC Γ}] = {← e.toC Γ};\n"

def Fn.signature (f : Fn) : Except String String := do
  let ps ← f.params.mapM fun (x, t) => return cDecl t (← cIdent x)
  let ps := if ps.isEmpty then "void" else ", ".intercalate ps
  return s!"{Ty.cName f.ret} {← cIdent f.name}({ps})"

def Fn.toC (f : Fn) : Except String String := do
  unless f.typeCheck do throw s!"{f.name}: does not type-check"
  let Γ := f.tyEnv
  let decls ← f.locals.mapM fun (x, t) => return s!"  {cDecl t (← cIdent x)};\n"
  let body ← f.body.toC Γ 1
  let ret ← match f.ret with
    | .unit => pure ""
    | _ => do pure s!"  return {← f.result.toC Γ};\n"
  return s!"{← f.signature} \{\n{String.join decls}{body}{ret}}\n"

/-- The fixed cPreamble: freestanding headers plus the TCB assumption about `int`. -/
def cPreamble : String :=
  "/* Generated by lean-c (LC). Do not edit. */\n" ++
  "#include <stdint.h>\n#include <stdbool.h>\n#include <limits.h>\n\n" ++
  "_Static_assert(INT_MAX == 2147483647, \"LC's integer-promotion rules assume 32-bit int\");\n\n"

/-- A translation unit. Function names must be distinct: C would reject (or, across files,
silently merge) two definitions of one name. M4's tester hit exactly this with `sub32`. -/
def cTranslationUnit (fs : List Fn) : Except String String := do
  let names := fs.map (·.name)
  unless names.eraseDups.length == names.length do
    throw s!"duplicate function names in translation unit: {names}"
  let bodies ← fs.mapM Fn.toC
  return cPreamble ++ "\n".intercalate bodies

end LC
