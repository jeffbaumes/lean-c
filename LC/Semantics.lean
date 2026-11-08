import LC.Syntax

/-!
# LC semantics

Two layers:

* `Expr.eval : Store → Expr → Option Val` is a **function**. Expressions are pure
  and always terminate, so nothing is gained by a relation. `none` means *the
  expression has no meaning*: undefined behaviour (signed overflow, division by
  zero, an oversized shift, reading an uninitialised local) or a dynamic type
  error.
* `Exec : Store → Stmt → Store → Prop` is an inductive **big-step relation**,
  in the style of *Concrete Semantics* §7.2. It has to be a relation because
  `while` may diverge.

**How UB shows up.** No rule fires, so there is no derivation: the program is
*stuck*. The program logic's triples promise that a derivation exists, so a
proved program cannot hit UB (design §3).

C references are to the C11 standard (N1570).
-/

namespace LC

/-! ## Stores -/

/-- Local variables, as a finite association list with at most one entry per name.
A missing name means *declared but uninitialised* (or not declared).

Why not `Ident → Option Val`? A closure-based store makes each update wrap the
old function, so a lookup after *k* assignments walks *k* closures. Loops become
quadratic in the interpreter and blow up under kernel evaluation (`decide`).
A first-order store is also something we can print and compare (`DecidableEq`). -/
abbrev Store := List (Ident × Val)

def Store.empty : Store := []

def Store.get : Store → Ident → Option Val
  | [], _ => none
  | (y, w) :: σ, x => if y = x then some w else Store.get σ x

def Store.set : Store → Ident → Val → Store
  | [], x, v => [(x, v)]
  | (y, w) :: σ, x, v => if y = x then (x, v) :: σ else (y, w) :: Store.set σ x v

@[simp] theorem Store.get_set_same (σ : Store) (x : Ident) (v : Val) :
    (σ.set x v).get x = some v := by
  induction σ with
  | nil => simp [Store.set, Store.get]
  | cons p σ ih =>
    obtain ⟨y, w⟩ := p
    by_cases h : y = x <;> simp_all [Store.set, Store.get]

@[simp] theorem Store.get_set_other (σ : Store) (x y : Ident) (v : Val) (h : y ≠ x) :
    (σ.set x v).get y = σ.get y := by
  induction σ with
  | nil => simp [Store.set, Store.get, Ne.symm h]
  | cons p σ ih =>
    obtain ⟨z, w⟩ := p
    by_cases hz : z = x
    · subst hz; simp [Store.set, Store.get, Ne.symm h]
    · simp only [Store.set, hz, ite_false, Store.get]; split <;> simp_all

/-! ## Integer arithmetic

The rule that encodes C's signed-integer semantics: compute the **mathematical**
result in `Int`. If it is representable in the type, that's the answer;
otherwise the behaviour is undefined (C11 §6.5¶5). Unsigned arithmetic is
defined to wrap (§6.2.5¶9), which is exactly `BitVec` arithmetic. -/

/-- `z` as a value of type `t`, if it is in range. -/
def IntTy.ofInt? (t : IntTy) (z : Int) : Option Val :=
  if t.min ≤ z ∧ z ≤ t.max then some (.int t (BitVec.ofInt t.bits z)) else none

/-- Binary operators on two integers of the *same* type `t`.
`land`/`lor` are handled in `Expr.eval` because they short-circuit. -/
def intBinOp (op : BinOp) (t : IntTy) (a b : BitVec t.bits) : Option Val :=
  let mk (r : BitVec t.bits) : Option Val := some (.int t r)
  match op with
  | .add => if t.signed then t.ofInt? (a.toInt + b.toInt) else mk (a + b)
  | .sub => if t.signed then t.ofInt? (a.toInt - b.toInt) else mk (a - b)
  | .mul => if t.signed then t.ofInt? (a.toInt * b.toInt) else mk (a * b)
  -- §6.5.5: division by zero is UB; signed `/` truncates toward zero (`Int.tdiv`).
  -- MIN / -1 is not representable, hence UB, and the `ofInt?` check catches it.
  | .div =>
    if b = 0 then none
    else if t.signed then t.ofInt? (a.toInt.tdiv b.toInt) else mk (a / b)
  -- §6.5.5¶6: if a/b is not representable, a%b is *also* UB (so MIN % -1 is UB).
  | .mod =>
    if b = 0 then none
    else if t.signed then
      (t.ofInt? (a.toInt.tdiv b.toInt)).bind fun _ => t.ofInt? (a.toInt.tmod b.toInt)
    else mk (a % b)
  | .band => mk (a &&& b)
  | .bor  => mk (a ||| b)
  | .bxor => mk (a ^^^ b)
  -- §6.5.7: a shift amount ≥ the width is UB. Signed shifts are UB or
  -- implementation-defined for negative operands, so LC allows unsigned shifts only.
  | .shl => if t.signed ∨ t.bits ≤ b.toNat then none else mk (a <<< b.toNat)
  | .shr => if t.signed ∨ t.bits ≤ b.toNat then none else mk (a >>> b.toNat)
  | .eq => some (.bool (a == b))
  | .ne => some (.bool (a != b))
  | .lt => some (.bool (if t.signed then a.slt b else a.ult b))
  | .le => some (.bool (if t.signed then a.sle b else a.ule b))
  | .land | .lor => none

def evalBinOp (op : BinOp) : Val → Val → Option Val
  | .int t a, .int t' b => if h : t' = t then intBinOp op t a (h ▸ b) else none
  | .bool a, .bool b =>
    match op with
    | .eq => some (.bool (a == b))
    | .ne => some (.bool (a != b))
    | _ => none
  | _, _ => none

def evalUnOp : UnOp → Val → Option Val
  -- §6.5.3.3: `-INT_MIN` is not representable, hence UB. Unsigned negation wraps.
  | .neg,  .int t a => if t.signed then t.ofInt? (-a.toInt) else some (.int t (-a))
  | .bnot, .int t a => some (.int t (~~~a))
  | .lnot, .bool b  => some (.bool (!b))
  | _, _ => none

/-- §6.3.1.3: conversion to an unsigned type reduces modulo 2ⁿ (defined).
Conversion to a signed type that can't hold the value is *implementation-defined*.
LC treats it as stuck, so programs never depend on it. -/
def evalCast (t : IntTy) (v : Val) : Option Val := do
  let z ← v.toInt?
  if t.signed then t.ofInt? z else some (.int t (BitVec.ofInt t.bits z))

/-! ## Expression evaluation -/

def Expr.eval (σ : Store) : Expr → Option Val
  | .lit v => some v
  | .var x => σ.get x
  | .unop op e => (e.eval σ).bind (evalUnOp op)
  -- `a && b`: if `a` is false, `b` is not evaluated (§6.5.13), so `b` may be
  -- undefined there. Example: `d != 0 && n / d > 1`.
  | .binop .land a b =>
    match a.eval σ with
    | some (.bool false) => some (.bool false)
    | some (.bool true) =>
      match b.eval σ with
      | some (.bool r) => some (.bool r)
      | _ => none
    | _ => none
  | .binop .lor a b =>
    match a.eval σ with
    | some (.bool true) => some (.bool true)
    | some (.bool false) =>
      match b.eval σ with
      | some (.bool r) => some (.bool r)
      | _ => none
    | _ => none
  | .binop op a b => do evalBinOp op (← a.eval σ) (← b.eval σ)
  | .cast t e => (e.eval σ).bind (evalCast t)

/-! ## Memory

A memory maps block ids to arrays of cells. The block layout (which blocks exist,
and how long each is) never changes: LC has no allocation yet, so buffers come from
the caller. Reading or writing outside a block, or in a block that doesn't exist,
has no meaning, and the program is stuck (C11 §6.5.6¶8, J.2). -/

abbrev Mem := List (Nat × List Val)

def Mem.cells : Mem → Nat → Option (List Val)
  | [], _ => none
  | (b, cs) :: μ, b' => if b = b' then some cs else Mem.cells μ b'

def Mem.setCells : Mem → Nat → List Val → Mem
  | [], _, _ => []
  | (b, cs) :: μ, b', cs' => if b = b' then (b, cs') :: μ else (b, cs) :: Mem.setCells μ b' cs'

/-- Read cell `k` of block `b`, if it exists. -/
def Mem.read (μ : Mem) (b k : Nat) : Option Val := (μ.cells b).bind (·[k]?)

/-- Write cell `k` of block `b`. Fails (`none`) out of bounds. -/
def Mem.write (μ : Mem) (b k : Nat) (v : Val) : Option Mem :=
  match μ.cells b with
  | some cs => if k < cs.length then some (μ.setCells b (cs.set k v)) else none
  | none => none

structure State where
  st  : Store
  mem : Mem
deriving DecidableEq, Repr, Inhabited

/-- Where `p[i]` points: pointer `p` must evaluate to `ptr t ⟨b, off⟩` and `i` to a `u32`.
The cell is `(b, off + i)`. -/
def Expr.evalAddr (st : Store) (p i : Expr) : Option (IntTy × Nat × Nat) :=
  match p.eval st, i.eval st with
  | some (.ptr t ⟨b, off⟩), some (.int ⟨false, .w32⟩ k) => some (t, b, off + k.toNat)
  | _, _ => none

/-! ## Statement execution (big-step)

A statement finishes in one of three ways (its **outcome**): normally, by `break`, or by
`return v`. `seq` and `while` propagate abrupt outcomes the way C does; a `break` ends the
innermost loop; a `return` unwinds to the enclosing call. This is the standard
treatment (e.g. CompCert's Clight `outcome`, Certora's Lean Clight post-conditions).

`Exec P σ s o σ'` runs inside a **program** `P`, which `call` uses to find functions by name.
-/

inductive Outcome where
  | normal
  | brk
  | ret (v : Val)
deriving DecidableEq, Repr, Inhabited

/-- What a call returns once its body has finished with outcome `o` in store `st`:
`return v` gives `v`, falling off the end evaluates `result`, and a stray `break` is
an error. The value must have the declared return type. -/
def Fn.finish (f : Fn) (o : Outcome) (st : Store) : Option Val :=
  let v? := match o with
    | .normal => f.result.eval st
    | .ret v => some v
    | .brk => none
  v?.bind fun v => if v.ty = f.ret then some v else none

/-- Bind parameters to arguments. Locals start uninitialised. -/
def Fn.initStore (f : Fn) (args : List Val) : Option Store :=
  if args.map Val.ty = f.params.map Prod.snd then
    some ((f.params.zip args).foldl (fun σ (p, v) => σ.set p.1 v) Store.empty)
  else none

/-- Assign the result of a call, if the call has a destination. -/
def Store.setOpt (st : Store) : Option Ident → Val → Store
  | some x, v => st.set x v
  | none, _ => st

/-- Evaluate call arguments, left to right (the order is unobservable: expressions are pure). -/
def Expr.evalList (st : Store) : List Expr → Option (List Val)
  | [] => some []
  | e :: es => do let v ← e.eval st; let vs ← Expr.evalList st es; return v :: vs

/-- `Exec P σ s o σ'`: in program `P`, running `s` from `σ` finishes with outcome `o` in
`σ'`. There is deliberately no rule for diverging or stuck executions. -/
inductive Exec (P : Program) : State → Stmt → Outcome → State → Prop
  | skip {σ} :
      Exec P σ .skip .normal σ
  | assign {st m x e v} :
      e.eval st = some v →
      Exec P ⟨st, m⟩ (.assign x e) .normal ⟨st.set x v, m⟩
  | seq {σ σ₁ σ₂ s₁ s₂ o} :
      Exec P σ s₁ .normal σ₁ → Exec P σ₁ s₂ o σ₂ →
      Exec P σ (.seq s₁ s₂) o σ₂
  /-- `s₁` finished abruptly (`break` or `return`): skip `s₂`. -/
  | seqAbrupt {σ σ₁ s₁ s₂ o} :
      Exec P σ s₁ o σ₁ → o ≠ .normal →
      Exec P σ (.seq s₁ s₂) o σ₁
  | iteTrue {σ σ' c s₁ s₂ o} :
      c.eval σ.st = some (.bool true) → Exec P σ s₁ o σ' →
      Exec P σ (.ite c s₁ s₂) o σ'
  | iteFalse {σ σ' c s₁ s₂ o} :
      c.eval σ.st = some (.bool false) → Exec P σ s₂ o σ' →
      Exec P σ (.ite c s₁ s₂) o σ'
  | whileTrue {σ σ₁ σ₂ c b o} :
      c.eval σ.st = some (.bool true) → Exec P σ b .normal σ₁ → Exec P σ₁ (.while c b) o σ₂ →
      Exec P σ (.while c b) o σ₂
  /-- `break` in the body ends the loop normally. -/
  | whileBreak {σ σ₁ c b} :
      c.eval σ.st = some (.bool true) → Exec P σ b .brk σ₁ →
      Exec P σ (.while c b) .normal σ₁
  /-- `return` in the body leaves the loop (and, at the call, the function). -/
  | whileRet {σ σ₁ c b v} :
      c.eval σ.st = some (.bool true) → Exec P σ b (.ret v) σ₁ →
      Exec P σ (.while c b) (.ret v) σ₁
  | whileFalse {σ c b} :
      c.eval σ.st = some (.bool false) →
      Exec P σ (.while c b) .normal σ
  /-- `x = p[i];` The cell must exist and hold a value of the pointer's element type. -/
  | load {st m x p i t b k v} :
      Expr.evalAddr st p i = some (t, b, k) →
      m.read b k = some v → v.ty = .int t →
      Exec P ⟨st, m⟩ (.load x p i) .normal ⟨st.set x v, m⟩
  /-- `p[i] = e;` The cell must exist, and `e` must have the element type. -/
  | store {st m m' p i e t b k v} :
      Expr.evalAddr st p i = some (t, b, k) →
      e.eval st = some v → v.ty = .int t →
      m.write b k v = some m' →
      Exec P ⟨st, m⟩ (.store p i e) .normal ⟨st, m'⟩
  | brk {σ} :
      Exec P σ .brk .brk σ
  | ret {σ e v} :
      e.eval σ.st = some v →
      Exec P σ (.ret e) (.ret v) σ
  /-- `x = f(args);` The callee runs in a fresh store (its parameters and locals) on the
  shared memory. Its result is assigned in the caller's store. -/
  | call {st m x f args g vs st₀ o σ₁ v} :
      P.find? f = some g → Expr.evalList st args = some vs → g.initStore vs = some st₀ →
      Exec P ⟨st₀, m⟩ g.body o σ₁ → g.finish o σ₁.st = some v →
      Exec P ⟨st, m⟩ (.call x f args) .normal ⟨st.setOpt x v, σ₁.mem⟩

/-! ## Functions -/

/-- `f.Returns P args m v m'`: in program `P`, calling `f` on `args` with memory `m`
terminates without UB, returns `v`, and leaves memory `m'`. -/
def Fn.Returns (f : Fn) (P : Program) (args : List Val) (m : Mem) (v : Val) (m' : Mem) : Prop :=
  ∃ st₀ o σ₁, f.initStore args = some st₀ ∧ Exec P ⟨st₀, m⟩ f.body o σ₁ ∧
    f.finish o σ₁.st = some v ∧ σ₁.mem = m'

end LC
