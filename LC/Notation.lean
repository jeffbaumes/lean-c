import LC.Syntax

/-!
# Lightweight notation for writing LC ASTs by hand

This is deliberately *not* a surface language yet (design §1: real syntax comes
once the AST settles). It is just enough operator overloading that
`v "s" + .cast .u64 (v "i")` reads like the C it stands for.

Comparisons get a trailing dot (`<.`, `==.`) because Lean's `<` and `=` must
produce a `Prop`, not an `Expr`.
-/

namespace LC

def Expr.v (x : Ident) : Expr := .var x
export Expr (v)

/-- Integer literal of type `t`. -/
def Expr.int (t : IntTy) (z : Int) : Expr := .lit (Val.ofInt t z)
def Expr.tt : Expr := .lit (.bool true)
def Expr.ff : Expr := .lit (.bool false)

namespace Val
def u8  (n : Int) : Val := ofInt .u8 n
def u16 (n : Int) : Val := ofInt .u16 n
def u32 (n : Int) : Val := ofInt .u32 n
def u64 (n : Int) : Val := ofInt .u64 n
def i8  (n : Int) : Val := ofInt .i8 n
def i16 (n : Int) : Val := ofInt .i16 n
def i32 (n : Int) : Val := ofInt .i32 n
def i64 (n : Int) : Val := ofInt .i64 n
end Val

namespace Expr
def u8  (n : Int) : Expr := .lit (.u8 n)
def u16 (n : Int) : Expr := .lit (.u16 n)
def u32 (n : Int) : Expr := .lit (.u32 n)
def u64 (n : Int) : Expr := .lit (.u64 n)
def i8  (n : Int) : Expr := .lit (.i8 n)
def i16 (n : Int) : Expr := .lit (.i16 n)
def i32 (n : Int) : Expr := .lit (.i32 n)
def i64 (n : Int) : Expr := .lit (.i64 n)
end Expr

instance : Add Expr := ⟨.binop .add⟩
instance : Sub Expr := ⟨.binop .sub⟩
instance : Mul Expr := ⟨.binop .mul⟩
instance : Div Expr := ⟨.binop .div⟩
instance : Mod Expr := ⟨.binop .mod⟩
instance : AndOp Expr := ⟨.binop .band⟩
instance : OrOp Expr := ⟨.binop .bor⟩
instance : HXor Expr Expr Expr := ⟨.binop .bxor⟩
instance : HShiftLeft Expr Expr Expr := ⟨.binop .shl⟩
instance : HShiftRight Expr Expr Expr := ⟨.binop .shr⟩
instance : Neg Expr := ⟨.unop .neg⟩
instance : Complement Expr := ⟨.unop .bnot⟩

scoped infix:50 " <. "  => Expr.binop BinOp.lt
scoped infix:50 " <=. " => Expr.binop BinOp.le
scoped infix:50 " >. "  => fun a b => Expr.binop BinOp.lt b a
scoped infix:50 " >=. " => fun a b => Expr.binop BinOp.le b a
scoped infix:50 " ==. " => Expr.binop BinOp.eq
scoped infix:50 " !=. " => Expr.binop BinOp.ne
scoped infixl:35 " &&. " => Expr.binop BinOp.land
scoped infixl:30 " ||. " => Expr.binop BinOp.lor
scoped prefix:max "!." => Expr.unop UnOp.lnot

scoped notation:40 x:max " ::= " e:41 => Stmt.assign x e
scoped infixr:20 " ;; " => Stmt.seq

/-- `block [s₁, s₂, s₃]` is `s₁ ;; s₂ ;; s₃`. -/
def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: ss => .seq s (block ss)

end LC
