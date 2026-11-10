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
@[simp] theorem Expr.eval_div (σ : Store) (a b : Expr) :
    (a / b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .div x) :=
  Expr.eval_binop σ .div a b (by decide) (by decide)
@[simp] theorem Expr.eval_mod (σ : Store) (a b : Expr) :
    (a % b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .mod x) :=
  Expr.eval_binop σ .mod a b (by decide) (by decide)
@[simp] theorem Expr.eval_band (σ : Store) (a b : Expr) :
    (a &&& b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .band x) :=
  Expr.eval_binop σ .band a b (by decide) (by decide)
@[simp] theorem Expr.eval_bor (σ : Store) (a b : Expr) :
    (a ||| b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .bor x) :=
  Expr.eval_binop σ .bor a b (by decide) (by decide)
@[simp] theorem Expr.eval_bxor (σ : Store) (a b : Expr) :
    (a ^^^ b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .bxor x) :=
  Expr.eval_binop σ .bxor a b (by decide) (by decide)
@[simp] theorem Expr.eval_shl (σ : Store) (a b : Expr) :
    (a <<< b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .shl x) :=
  Expr.eval_binop σ .shl a b (by decide) (by decide)
@[simp] theorem Expr.eval_shr (σ : Store) (a b : Expr) :
    (a >>> b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp .shr x) :=
  Expr.eval_binop σ .shr a b (by decide) (by decide)
@[simp] theorem Expr.eval_binop_simple (σ : Store) (op : BinOp) (a b : Expr)
    (h : op ∈ [.add, .sub, .mul, .div, .mod, .band, .bor, .bxor, .shl, .shr, .eq, .ne, .lt, .le]) :
    (Expr.binop op a b).eval σ = (a.eval σ).bind fun x => (b.eval σ).bind (evalBinOp op x) :=
  Expr.eval_binop σ op a b (by cases op <;> simp_all) (by cases op <;> simp_all)

/-! The short-circuit operators `&&.` and `||.`. The right operand is wrapped in `Expr.lorK` /
`Expr.landK`, which `simp` keeps closed until it knows enough: the left value (`true`/`false`
picks a side) or a boolean right value (the result is `s || r` / `s && r`). Unfolding to an
`if` instead lets `simp` rewrite `decide p = true` to `p`, and then the `if` never closes. -/

/-- The boolean inside a value, if it is one. -/
def Val.bool? : Val → Option Bool
  | .bool b => some b
  | _ => none

@[simp] theorem Val.bool?_bool (b : Bool) : (Val.bool b).bool? = some b := rfl

/-- `s || k`, where `k` is evaluated only if `s` is false. -/
def Expr.lorK (s : Bool) (k : Option Val) : Option Val := if s then some (.bool true) else k
/-- `s && k`, where `k` is evaluated only if `s` is true. -/
def Expr.landK (s : Bool) (k : Option Val) : Option Val := if s then k else some (.bool false)

@[simp] theorem Expr.lorK_true (k : Option Val) : Expr.lorK true k = some (.bool true) := rfl
@[simp] theorem Expr.lorK_false (k : Option Val) : Expr.lorK false k = k := rfl
@[simp] theorem Expr.lorK_bool (s r : Bool) :
    Expr.lorK s (some (.bool r)) = some (.bool (s || r)) := by cases s <;> rfl
@[simp] theorem Expr.landK_true (k : Option Val) : Expr.landK true k = k := rfl
@[simp] theorem Expr.landK_false (k : Option Val) : Expr.landK false k = some (.bool false) := rfl
@[simp] theorem Expr.landK_bool (s r : Bool) :
    Expr.landK s (some (.bool r)) = some (.bool (s && r)) := by cases s <;> rfl

@[simp] theorem Expr.eval_lor (σ : Store) (a b : Expr) :
    (Expr.binop .lor a b).eval σ = (a.eval σ).bind fun x => x.bool?.bind fun s =>
      Expr.lorK s (((b.eval σ).bind Val.bool?).map Val.bool) := by
  simp only [Expr.eval, Expr.lorK]
  rcases Expr.eval σ a with _ | (_ | ⟨_ | _⟩ | _ | _) <;>
    (try rfl) <;> rcases Expr.eval σ b with _ | (_ | _ | _ | _) <;> rfl

@[simp] theorem Expr.eval_land (σ : Store) (a b : Expr) :
    (Expr.binop .land a b).eval σ = (a.eval σ).bind fun x => x.bool?.bind fun s =>
      Expr.landK s (((b.eval σ).bind Val.bool?).map Val.bool) := by
  simp only [Expr.eval, Expr.landK]
  rcases Expr.eval σ a with _ | (_ | ⟨_ | _⟩ | _ | _) <;>
    (try rfl) <;> rcases Expr.eval σ b with _ | (_ | _ | _ | _) <;> rfl

@[simp] theorem evalBinOp_int (op : BinOp) (t : IntTy) (a b : BitVec t.bits) :
    evalBinOp op (.int t a) (.int t b) = intBinOp op t a b := by
  simp [evalBinOp]

@[simp] theorem evalCast_int (t t' : IntTy) (a : BitVec t'.bits) :
    evalCast t (.int t' a) =
      let z : Int := if t'.signed then a.toInt else a.toNat
      if t.signed then t.ofInt? z else some (.int t (BitVec.ofInt t.bits z)) := by
  simp [evalCast, Val.toInt?]

end LC
