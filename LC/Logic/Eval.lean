import LC.Semantics
import LC.Notation

/-!
# Simp lemmas for symbolic evaluation

`wp_assign` and friends leave goals like `(v "s" + .cast .u64 (v "i")).eval σ = some ?v`
for a *concrete* store `σ`. These lemmas let `simp [lc_eval]` compute such goals down
to plain `BitVec`/`Nat` facts.
-/

namespace LC

@[simp] theorem IntTy.bits_u8  : IntTy.u8.bits = 8 := rfl
@[simp] theorem IntTy.bits_u16 : IntTy.u16.bits = 16 := rfl
@[simp] theorem IntTy.bits_u32 : IntTy.u32.bits = 32 := rfl
@[simp] theorem IntTy.bits_u64 : IntTy.u64.bits = 64 := rfl
@[simp] theorem IntTy.bits_i8  : IntTy.i8.bits = 8 := rfl
@[simp] theorem IntTy.bits_i16 : IntTy.i16.bits = 16 := rfl
@[simp] theorem IntTy.bits_i32 : IntTy.i32.bits = 32 := rfl
@[simp] theorem IntTy.bits_i64 : IntTy.i64.bits = 64 := rfl

@[simp] theorem Store.get_cons (y x : Ident) (w : Val) (σ : Store) :
    Store.get ((y, w) :: σ) x = if y = x then some w else σ.get x := rfl
@[simp] theorem Store.get_nil (x : Ident) : Store.get [] x = none := rfl
@[simp] theorem Store.set_cons (y x : Ident) (w v : Val) (σ : Store) :
    Store.set ((y, w) :: σ) x v = if y = x then (x, v) :: σ else (y, w) :: σ.set x v := rfl
@[simp] theorem Store.set_nil (x : Ident) (v : Val) : Store.set [] x v = [(x, v)] := rfl

@[simp] theorem Expr.eval_lit (σ : Store) (val : Val) : (Expr.lit val).eval σ = some val := rfl
@[simp] theorem Expr.eval_tt (σ : Store) : Expr.tt.eval σ = some (.bool true) := rfl
@[simp] theorem Expr.eval_ff (σ : Store) : Expr.ff.eval σ = some (.bool false) := rfl
@[simp] theorem Expr.eval_var (σ : Store) (x : Ident) : (Expr.var x).eval σ = σ.get x := rfl
@[simp] theorem Expr.eval_v (σ : Store) (x : Ident) : (v x).eval σ = σ.get x := rfl
@[simp] theorem Expr.eval_cast (σ : Store) (t : IntTy) (e : Expr) :
    (Expr.cast t e).eval σ = (e.eval σ).bind (evalCast t) := rfl
@[simp] theorem Expr.eval_unop (σ : Store) (op : UnOp) (e : Expr) :
    (Expr.unop op e).eval σ = (e.eval σ).bind (evalUnOp op) := rfl

/-- Non-short-circuit binary operators evaluate both sides. -/
theorem Expr.eval_binop (σ : Store) (op : BinOp) (a b : Expr)
    (h₁ : op ≠ .land) (h₂ : op ≠ .lor) :
    (Expr.binop op a b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind fun y => evalBinOp op x y := by
  cases op <;> simp_all [Expr.eval, Option.bind] <;> rfl

-- Specialisations simp can use without side conditions.
@[simp] theorem Expr.eval_add (σ : Store) (a b : Expr) :
    (a + b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .add x) :=
  Expr.eval_binop σ .add a b (by decide) (by decide)
@[simp] theorem Expr.eval_sub (σ : Store) (a b : Expr) :
    (a - b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .sub x) :=
  Expr.eval_binop σ .sub a b (by decide) (by decide)
@[simp] theorem Expr.eval_mul (σ : Store) (a b : Expr) :
    (a * b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .mul x) :=
  Expr.eval_binop σ .mul a b (by decide) (by decide)
@[simp] theorem Expr.eval_binop_simple (σ : Store) (op : BinOp) (a b : Expr)
    (h : op ∈ [.add, .sub, .mul, .div, .mod, .band, .bor, .bxor, .shl, .shr, .eq, .ne, .lt, .le]) :
    (Expr.binop op a b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp op x) :=
  Expr.eval_binop σ op a b (by cases op <;> simp_all) (by cases op <;> simp_all)

@[simp] theorem evalBinOp_int (op : BinOp) (t : IntTy) (a b : BitVec t.bits) :
    evalBinOp op (.int t a) (.int t b) = intBinOp op t a b := by
  simp [evalBinOp]

@[simp] theorem evalCast_int (t t' : IntTy) (a : BitVec t'.bits) :
    evalCast t (.int t' a) =
      let z : Int := if t'.signed then a.toInt else a.toNat
      if t.signed then t.ofInt? z else some (.int t (BitVec.ofInt t.bits z)) := by
  simp [evalCast, Val.toInt?]

end LC
