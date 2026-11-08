/-
A4 — A deep embedding in 15 minutes.            Run:  lean exercises/core/A4_Expr.lean

A *deep* embedding represents programs as data (an inductive type) and gives
them meaning with a separate function. Our LC language will be exactly this,
scaled up. Fill in the three `sorry`s.
-/

inductive Expr where
  | lit : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
deriving Repr

def Env := String → Int

-- (1) The semantics. One line per constructor.
def Expr.eval (ρ : Env) : Expr → Int
  | _ => sorry

-- A program transformation: fold constant subtrees.
def Expr.constFold : Expr → Expr
  | .add a b => match a.constFold, b.constFold with
    | .lit x, .lit y => .lit (x + y)
    | a', b' => .add a' b'
  | .mul a b => match a.constFold, b.constFold with
    | .lit x, .lit y => .lit (x * y)
    | a', b' => .mul a' b'
  | e => e

-- (2) Uncomment once `eval` is done; expect 17.
-- #eval (Expr.add (.lit 2) (.mul (.lit 3) (.var "x"))).eval (fun _ => 5)

-- (3) The transformation preserves meaning, for every environment.
--     Hint: `induction e`, then in the add/mul cases `simp only [constFold]; split <;> simp_all [eval]`.
theorem Expr.constFold_correct (ρ : Env) (e : Expr) :
    e.constFold.eval ρ = e.eval ρ := by
  sorry

/- (4) Think (write 2–3 sentences as a comment below):
   Write `fun x : Int => 2 + 3 * x` — the *shallow* version of the same program.
   Which of these can you do with the shallow version, and which only with `Expr`?
     a. evaluate it        b. prove it equals `fun x => 3 * x + 2`
     c. print it as C text d. state "constFold preserves meaning" for *all* programs
-/
