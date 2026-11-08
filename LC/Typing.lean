import LC.Syntax
import LC.Semantics

/-!
# Static type checking

The semantics is *dynamically* checked: an ill-typed operation is just stuck. The
type checker is a static, decidable approximation that rejects programs that
would get stuck **for type reasons** (adding a `u8` to a `u32`, branching on an
integer, assigning across types) before they run. That matters for two reasons:

1. The C printer needs every expression's type to emit correct casts.
2. It removes the cheap obligations from proofs, leaving only the value-dependent
   ones (overflow, bounds, division by zero).

Type preservation (`Expr.typeOf_sound`, `Exec.preserves_typed`) is proved in
`LC/TypingSound.lean`.
-/

namespace LC

abbrev TyEnv := Ident → Option Ty

def Expr.typeOf (Γ : TyEnv) : Expr → Option Ty
  -- Pointer literals would forge addresses: only parameters can hold pointers.
  | .lit (.ptr _ _) => none
  | .lit v => some v.ty
  | .var x => Γ x
  | .unop op e => do
    match op, ← e.typeOf Γ with
    | .neg,  .int t => some (.int t)
    | .bnot, .int t => some (.int t)
    | .lnot, .bool  => some .bool
    | _, _ => none
  | .binop op a b => do
    let ta ← a.typeOf Γ
    let tb ← b.typeOf Γ
    if ta ≠ tb then none else
    match op, ta with
    | .add, .int t | .sub, .int t | .mul, .int t | .div, .int t | .mod, .int t
    | .band, .int t | .bor, .int t | .bxor, .int t => some (.int t)
    | .shl, .int t | .shr, .int t => if t.signed then none else some (.int t)
    | .eq, .int _ | .ne, .int _ | .eq, .bool | .ne, .bool => some .bool
    | .lt, .int _ | .le, .int _ => some .bool
    | .land, .bool | .lor, .bool => some .bool
    | _, _ => none
  | .cast t e => do
    match ← e.typeOf Γ with
    | .int _ => some (.int t)
    | _ => none

/-- Function signatures (parameter types, return type), looked up by name. -/
abbrev Sigs := Ident → Option (List Ty × Ty)

def Program.sigs (P : Program) : Sigs :=
  fun f => (P.find? f).map fun g => (g.params.map Prod.snd, g.ret)

/-- `s.typeCheck Γ sg rt inLoop`: `s` is well-typed under locals `Γ` and callee signatures
`sg`, inside a function returning `rt`. `inLoop` says whether `break` is allowed here. -/
def Stmt.typeCheck (Γ : TyEnv) (sg : Sigs) (rt : Ty) (inLoop : Bool) : Stmt → Bool
  | .skip => true
  | .assign x e => (Γ x).isSome && Γ x == e.typeOf Γ
  | .seq s₁ s₂ => s₁.typeCheck Γ sg rt inLoop && s₂.typeCheck Γ sg rt inLoop
  | .ite c s₁ s₂ => c.typeOf Γ == some .bool && s₁.typeCheck Γ sg rt inLoop && s₂.typeCheck Γ sg rt inLoop
  | .while c b => c.typeOf Γ == some .bool && b.typeCheck Γ sg rt true
  | .load x p i =>
    match p.typeOf Γ with
    | some (.ptr t) => i.typeOf Γ == some (.int .u32) && Γ x == some (.int t)
    | _ => false
  | .store p i e =>
    match p.typeOf Γ with
    | some (.ptr t) => i.typeOf Γ == some (.int .u32) && e.typeOf Γ == some (.int t)
    | _ => false
  | .brk => inLoop
  | .ret e => e.typeOf Γ == some rt
  | .call x f args =>
    match sg f with
    | some (ps, r) =>
      args.map (·.typeOf Γ) == ps.map some &&
        (match x with | some x => Γ x == some r | none => true)
    | none => false

def Fn.tyEnv (f : Fn) : TyEnv := fun x => (f.params ++ f.locals).lookup x

/-- Well-formedness of a function inside program `P` (default: no callees): distinct names,
a well-typed body, and a result of the declared type. -/
def Fn.typeCheck (f : Fn) (P : Program := []) : Bool :=
  let names := (f.params ++ f.locals).map Prod.fst
  names.eraseDups.length == names.length &&
  f.body.typeCheck f.tyEnv P.sigs f.ret false &&
  f.result.typeOf f.tyEnv == some f.ret

end LC
