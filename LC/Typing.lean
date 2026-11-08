import LC.Syntax

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

def Stmt.typeCheck (Γ : TyEnv) : Stmt → Bool
  | .skip => true
  | .assign x e => (Γ x).isSome && Γ x == e.typeOf Γ
  | .seq s₁ s₂ => s₁.typeCheck Γ && s₂.typeCheck Γ
  | .ite c s₁ s₂ => c.typeOf Γ == some .bool && s₁.typeCheck Γ && s₂.typeCheck Γ
  | .while c b => c.typeOf Γ == some .bool && b.typeCheck Γ
  | .load x p i =>
    match p.typeOf Γ with
    | some (.ptr t) => i.typeOf Γ == some (.int .u32) && Γ x == some (.int t)
    | _ => false
  | .store p i e =>
    match p.typeOf Γ with
    | some (.ptr t) => i.typeOf Γ == some (.int .u32) && e.typeOf Γ == some (.int t)
    | _ => false

def Fn.tyEnv (f : Fn) : TyEnv := fun x => (f.params ++ f.locals).lookup x

/-- Well-formedness of a function: distinct names, a well-typed body, and a result of the declared type. -/
def Fn.typeCheck (f : Fn) : Bool :=
  let names := (f.params ++ f.locals).map Prod.fst
  names.eraseDups.length == names.length &&
  f.body.typeCheck f.tyEnv &&
  f.result.typeOf f.tyEnv == some f.ret

end LC
