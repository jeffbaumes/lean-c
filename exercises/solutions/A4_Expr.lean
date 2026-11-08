-- Solution to exercises/core/A4_Expr.lean. (4): only (a),(b) work shallowly; (c),(d) need the AST as data.
-- deep embedding warm-up used in Core assignment C3
inductive Expr where
  | lit : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
deriving Repr

def Env := String → Int

def Expr.eval (ρ : Env) : Expr → Int
  | .lit n => n
  | .var x => ρ x
  | .add a b => a.eval ρ + b.eval ρ
  | .mul a b => a.eval ρ * b.eval ρ

def Expr.constFold : Expr → Expr
  | .add a b => match a.constFold, b.constFold with
    | .lit x, .lit y => .lit (x + y)
    | a', b' => .add a' b'
  | .mul a b => match a.constFold, b.constFold with
    | .lit x, .lit y => .lit (x * y)
    | a', b' => .mul a' b'
  | e => e

theorem Expr.constFold_correct (ρ : Env) (e : Expr) : e.constFold.eval ρ = e.eval ρ := by
  induction e with
  | add a b iha ihb =>
    simp only [constFold]; split <;> simp_all [eval]
  | mul a b iha ihb =>
    simp only [constFold]; split <;> simp_all [eval]
  | _ => rfl

#eval (Expr.add (.lit 2) (.mul (.lit 3) (.var "x"))).eval (fun _ => 5)
