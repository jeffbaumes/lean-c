/-!
# LC syntax (Milestone 1)

The *deep* embedding: LC programs are ordinary Lean data. Everything else (the
semantics, the interpreter, the program logic, the C printer) is a function
or relation over these types.

Design references: `docs/phase2-design.md` §1 (deep core), §2 (subset), §4 (integers).

Milestone-1 scope: fixed-width integers, booleans, locals, arithmetic, `if`,
`while`, and one function body with a final `return` expression. Memory and
pointers arrive in Milestone 3.
-/

namespace LC

/-! ## Types -/

/-- The four C integer widths we support. There is no `int`, `long` or `char`:
their width depends on the implementation, ours never does. -/
inductive Width
  | w8 | w16 | w32 | w64
deriving DecidableEq, Repr, Inhabited

@[reducible] def Width.bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- An integer type: signedness × width. `⟨false, .w32⟩` is `uint32_t`. -/
structure IntTy where
  signed : Bool
  width  : Width
deriving DecidableEq, Repr, Inhabited

namespace IntTy
abbrev u8  : IntTy := ⟨false, .w8⟩
abbrev u16 : IntTy := ⟨false, .w16⟩
abbrev u32 : IntTy := ⟨false, .w32⟩
abbrev u64 : IntTy := ⟨false, .w64⟩
abbrev i8  : IntTy := ⟨true, .w8⟩
abbrev i16 : IntTy := ⟨true, .w16⟩
abbrev i32 : IntTy := ⟨true, .w32⟩
abbrev i64 : IntTy := ⟨true, .w64⟩

abbrev bits (t : IntTy) : Nat := t.width.bits

/-- Smallest and largest mathematical integers representable in `t`. -/
def min (t : IntTy) : Int := if t.signed then -(2 ^ (t.bits - 1) : Int) else 0
def max (t : IntTy) : Int := if t.signed then (2 ^ (t.bits - 1) : Int) - 1 else (2 ^ t.bits : Int) - 1
end IntTy

/-- LC types. `ptr t` is a pointer into an array of `t` (C: `t *`). Structs come in M5. -/
inductive Ty
  | int  (t : IntTy)
  | bool
  | ptr  (t : IntTy)
  | unit
deriving DecidableEq, Repr, Inhabited

/-! ## Pointers (Milestone 3)

A pointer is a **block** and an **offset** (design §3; CompCert's and Low\*'s
memory models). A block is one array object, such as a buffer the caller passed in.
Offsets count *elements*, not bytes, because each block holds cells of one type
("typed-cell blocks"). Pointer↔integer casts don't exist, so a pointer can never
be forged and C's provenance rules (ISO TS 6010) are respected by construction. -/
structure Ptr where
  blk : Nat
  off : Nat
deriving DecidableEq, Repr, Inhabited

/-! ## Values -/

/-- A runtime value. An integer carries its type, and its payload is a
bit-vector of exactly that width, so a `u8` holding 300 cannot be constructed.

`BitVec` is Lean's fixed-width bit-vector. It is what `bv_decide` reasons about,
and Certora's Lean Clight uses the same representation. -/
inductive Val
  | int  (t : IntTy) (bv : BitVec t.bits)
  | bool (b : Bool)
  | ptr  (t : IntTy) (p : Ptr)
  | unit
deriving DecidableEq, Inhabited

/-- Print values the way you'd write them: `55u64`, `-3i32`, `true`. -/
def Val.toString : Val → String
  | .int t bv =>
    let z : Int := if t.signed then bv.toInt else bv.toNat
    s!"{z}{if t.signed then "i" else "u"}{t.bits}"
  | .bool b => if b then "true" else "false"
  | .ptr _ p => s!"&b{p.blk}[{p.off}]"
  | .unit => "()"

instance : ToString Val := ⟨Val.toString⟩
instance : Repr Val := ⟨fun v _ => v.toString⟩

/-- Integer value of type `t` from a mathematical integer (wrapping mod 2ⁿ).
Used for literals, so `Val.ofInt .u8 300` is `44u8`: there is no UB in a literal. -/
def Val.ofInt (t : IntTy) (z : Int) : Val := .int t (BitVec.ofInt t.bits z)

def Val.ty : Val → Ty
  | .int t _ => .int t
  | .bool _  => .bool
  | .ptr t _ => .ptr t
  | .unit    => .unit

/-- The *mathematical* integer an integer value denotes: two's complement for
signed types, plain binary for unsigned. C's arithmetic rules are stated in terms
of this number (C11 §6.2.6.2, §6.3.1.3). -/
def Val.toInt? : Val → Option Int
  | .int t bv => some (if t.signed then bv.toInt else bv.toNat)
  | _         => none

/-! ## Expressions

Expressions are **pure**: no assignment, no calls, no memory reads. In C the
evaluation order of operands is unspecified, but an expression that can't have
side effects can't observe the order (design §2, the Clight "temporaries"
discipline). -/

inductive BinOp
  -- arithmetic (both operands have the same integer type)
  | add | sub | mul | div | mod
  -- bitwise (same integer type)
  | band | bor | bxor
  -- shifts (unsigned only in LC; same type; amount < width)
  | shl | shr
  -- comparisons (same integer type, or both bool for eq/ne) → bool
  | eq | ne | lt | le
  -- logical, short-circuiting like C's `&&` and `||` (bool)
  | land | lor
deriving DecidableEq, Repr, Inhabited

inductive UnOp
  | neg    -- arithmetic negation `-e`
  | bnot   -- bitwise complement `~e`
  | lnot   -- logical not `!e`
deriving DecidableEq, Repr, Inhabited

abbrev Ident := String

inductive Expr
  | lit   (v : Val)
  | var   (x : Ident)
  | unop  (op : UnOp) (e : Expr)
  | binop (op : BinOp) (a b : Expr)
  /-- Explicit width/signedness conversion. LC has no implicit conversions. -/
  | cast  (t : IntTy) (e : Expr)
deriving DecidableEq, Repr, Inhabited

/-! ## Statements -/

/-! ## Statements

Memory is accessed only by statements, never inside expressions, so expressions
stay pure (Clight makes the same choice). Indexing is `p[i]` with a `u32` index,
which is the Low\* `index`/`upd` style. There is no general pointer arithmetic yet. -/

inductive Stmt
  | skip
  | assign (x : Ident) (e : Expr)
  | seq    (s₁ s₂ : Stmt)
  | ite    (c : Expr) (s₁ s₂ : Stmt)
  | while  (c : Expr) (body : Stmt)
  /-- `x = p[i];` -/
  | load   (x : Ident) (p : Expr) (i : Expr)
  /-- `p[i] = e;` -/
  | store  (p : Expr) (i : Expr) (e : Expr)
deriving DecidableEq, Repr, Inhabited

/-! ## Functions

A function is: typed parameters, typed locals, a body, and a result expression
evaluated after the body (one `return` at the end). Early `return` and `break`
need a richer outcome type. They were planned for M3 but are deferred to M5,
since neither M3 target needs them. -/

structure Fn where
  name   : Ident
  params : List (Ident × Ty)
  locals : List (Ident × Ty)
  body   : Stmt
  ret    : Ty
  result : Expr
deriving Repr, Inhabited

end LC
