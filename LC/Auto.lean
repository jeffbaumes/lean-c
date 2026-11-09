import LC.Auto.Attr
import LC.Spec

/-!
# `lc_auto`: the routine part of an LC proof

A proof about an LC function should be the invariants, the variants, and the lemmas that are
really about the problem. Everything else is bookkeeping, and `lc_auto` does it:

* **Symbolic execution (a VC generator).** On a goal `swp P s Q st h` or `swpo P s Q st h` it
  applies the rule for `s`: `skip`, assignment, `;`, `if`, load, store, `break`, `return`.
  Each expression is evaluated by `simp` with the store facts in context, and the computed value
  is fed back (`exact rfl` on `e.eval st = some ?v`). It stops at `while` (`lc_while I μ` applies
  the loop rule and continues on its four obligations) and at `call` (`lc_call hfind spec init`).
* **Store facts.** Hypotheses `st.get x = some v` are rewritten through any number of
  `Store.set`s, so they survive unrelated assignments. Invariants `I st h` are unfolded and
  destructured, equations between variables are substituted, and `a ≤ b`, `b ≤ a` give `a = b`.
* **Heap (a small `sep_simp`).** For `p[i]` it searches the `∗`-trees of `array`s in context for
  the one that owns the cell (`array_get_at`, `star_get_left/right`). After `p[i] = e` it
  rewrites that heap fact to one about the updated heap (`array_update_at`,
  `star_update_left/right`) and generalizes the new heap, so later loads see the new contents.
  A final `∗`-assertion is matched shape-for-shape (`star_mono`), leaving list equalities.
* **`BitVec` → `Nat`.** The `lc_simp` set turns `BitVec.ofNat` arithmetic into `Nat` arithmetic
  when it's in range (`bv_sub`, `bv_udiv`, `bv_mul`, `Nat.mod_eq_of_lt`, …), discharging the
  range side conditions with `omega`.
* **Pure goals.** Existential witnesses are found by unifying equations such as
  `(st.set "i" (nu32 (i+1))).get "i" = some (nu32 ?k)`. The leaves are closed with `rfl`,
  `assumption`, `omega`, `simp`, and finally `grind`. What can't be closed is left, simplified.

`lc_auto [foo, bar]` also unfolds or rewrites with `foo`, `bar`: pass your invariant, variant
and any spec lemmas (like `psum_succ`). `set_option trace.lc_auto true` shows what it does.

**Soundness.** `lc_auto` only ever applies proved lemmas; everything it produces is checked by
the kernel. It runs with error recovery off, so a sub-tactic that fails never turns into a
silent `sorry`.
-/

open Lean Meta Elab Tactic

namespace LC

/-! ## Rule variants in the shape the generator wants -/

theorem swpo_skip {Pr : Program} {Q : Outcome → SProp} {st : Store} {h : Heap}
    (hq : Q .normal st h) : swpo Pr .skip Q st h := swpo_of_swp (swp_skip hq)

theorem swpo_assign {Pr : Program} {x : Ident} {e : Expr} {Q : Outcome → SProp} {st : Store}
    {h : Heap} {v : Val} (hv : e.eval st = some v) (hq : Q .normal (st.set x v) h) :
    swpo Pr (.assign x e) Q st h := swpo_of_swp (swp_assign hv hq)

theorem swpo_load {Pr : Program} {x : Ident} {p i : Expr} {Q : Outcome → SProp} {st : Store}
    {h : Heap} {t : IntTy} {b k : Nat} {v : Val}
    (ha : Expr.evalAddr st p i = some (t, b, k)) (hcell : h (b, k) = some v)
    (hty : v.ty = .int t) (hq : Q .normal (st.set x v) h) : swpo Pr (.load x p i) Q st h :=
  swpo_of_swp (swp_load ha hcell hty hq)

theorem swpo_store {Pr : Program} {p i e : Expr} {Q : Outcome → SProp} {st : Store} {h : Heap}
    {t : IntTy} {b k : Nat} {v v₀ : Val}
    (ha : Expr.evalAddr st p i = some (t, b, k)) (hv : e.eval st = some v)
    (hty : v.ty = .int t) (hcell : h (b, k) = some v₀)
    (hq : Q .normal st (h.update (b, k) v)) : swpo Pr (.store p i e) Q st h :=
  swpo_of_swp (swp_store ha hv hty hcell hq)

/-- `if`, with the condition computed once: each branch gets the condition's value as a
hypothesis, so a case split falls out of `intro`. -/
theorem swp_ite_eval {Pr : Program} {c : Expr} {s₁ s₂ : Stmt} {Q : SProp} {st : Store}
    {h : Heap} {b : Bool} (hc : c.eval st = some (.bool b))
    (h₁ : b = true → swp Pr s₁ Q st h) (h₂ : b = false → swp Pr s₂ Q st h) :
    swp Pr (.ite c s₁ s₂) Q st h := by
  apply swp_ite; cases b
  · exact .inr ⟨hc, h₂ rfl⟩
  · exact .inl ⟨hc, h₁ rfl⟩

theorem swpo_ite_eval {Pr : Program} {c : Expr} {s₁ s₂ : Stmt} {Q : Outcome → SProp}
    {st : Store} {h : Heap} {b : Bool} (hc : c.eval st = some (.bool b))
    (h₁ : b = true → swpo Pr s₁ Q st h) (h₂ : b = false → swpo Pr s₂ Q st h) :
    swpo Pr (.ite c s₁ s₂) Q st h := by
  apply swpo_ite; cases b
  · exact .inr ⟨hc, h₂ rfl⟩
  · exact .inl ⟨hc, h₁ rfl⟩

/-! ## Heap lemmas in the shape the cell search wants -/

theorem array_get_at {p : Ptr} {xs : List Val} {h : Heap} {a : Addr} (ha : array p xs h)
    (h₁ : a.1 = p.blk) (h₂ : p.off ≤ a.2) (h₃ : a.2 - p.off < xs.length) :
    h a = some xs[a.2 - p.off]! := by
  obtain ⟨b, k⟩ := a; simp only at h₁ h₂ h₃ ⊢; subst h₁
  have := array_get ha h₃; rw [Nat.add_sub_cancel' h₂] at this
  rw [this, getElem!_pos xs _ (by omega)]

theorem array_update_at {p : Ptr} {xs : List Val} {h : Heap} {a : Addr} (v : Val)
    (ha : array p xs h) (h₁ : a.1 = p.blk) (h₂ : p.off ≤ a.2) (h₃ : a.2 - p.off < xs.length) :
    array p (xs.set (a.2 - p.off) v) (h.update a v) := by
  obtain ⟨b, k⟩ := a; simp only at h₁ h₂ h₃ ⊢; subst h₁
  have := array_update ha h₃ v; rwa [Nat.add_sub_cancel' h₂] at this

theorem ne_none_of_eq_some {α} {o : Option α} {v : α} (h : o = some v) : o ≠ none := by
  simp [h]

theorem array_congr {p q : Ptr} {xs ys : List Val} {h : Heap} (ha : array p xs h)
    (hp : p = q) (hxs : xs = ys) : array q ys h := hp ▸ hxs ▸ ha

/-! ## The simp set -/

attribute [lc_simp] Expr.u8 Expr.u16 Expr.u32 Expr.u64 Expr.i8 Expr.i16 Expr.i32 Expr.i64
  Val.u8 Val.u16 Val.u32 Val.u64 Val.i8 Val.i16 Val.i32 Val.i64 Val.ofInt
  intBinOp BitVec.ult BitVec.ule Expr.evalAddr BitVec.ofNat_add_ofNat Nat.mod_eq_of_lt
  bv_mul bv_sub bv_udiv Val.ty
  List.getElem_map List.length_map Nat.add_sub_cancel_left List.getElem?_eq_none getElem!_pos
  Expr.evalList Store.setOpt evalUnOp

/-- Equality of in-range bit-vector literals is equality of the numbers. -/
@[lc_simp] theorem bv_ofNat_eq {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    (BitVec.ofNat w a = BitVec.ofNat w b) ↔ a = b := by
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · rintro rfl; rfl

@[lc_simp] theorem Fn.finish_normal_eq (f : Fn) (st : Store) :
    f.finish .normal st = (f.result.eval st).bind fun v => if v.ty = f.ret then some v else none :=
  rfl
@[lc_simp] theorem Fn.finish_ret_eq (f : Fn) (st : Store) (v : Val) :
    f.finish (.ret v) st = if v.ty = f.ret then some v else none := rfl
@[lc_simp] theorem Fn.finish_brk_eq (f : Fn) (st : Store) : f.finish .brk st = none := rfl

/-- `f.result` and `f.ret` for a concrete function `f`. -/
dsimproc [lc_simp] reduceFnResult (Fn.result _) := fun e => do
  let_expr Fn.result f := e | return .continue
  unless f.isConst do return .continue
  return .done (← whnfD e)

dsimproc [lc_simp] reduceFnRet (Fn.ret _) := fun e => do
  let_expr Fn.ret f := e | return .continue
  unless f.isConst do return .continue
  return .done (← whnfD e)

dsimproc [lc_simp] reduceFnParams (Fn.params _) := fun e => do
  let_expr Fn.params f := e | return .continue
  unless f.isConst do return .continue
  return .done (← whnfD e)

end LC

namespace LC.Auto

initialize registerTraceClass `lc_auto

/-- Is `ty` a linear-arithmetic fact over `Nat`/`Int` that `omega` can use? -/
partial def isArith (ty : Lean.Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  let numTy (α : Lean.Expr) : Bool := α.isConstOf ``Nat || α.isConstOf ``Int
  match_expr ty with
  | Not p => isArith p
  | And a b => return (← isArith a) && (← isArith b)
  | Or a b => return (← isArith a) && (← isArith b)
  | Iff a b => return (← isArith a) && (← isArith b)
  | Eq α _ _ => return numTy α
  | Ne α _ _ => return numTy α
  | LE.le α _ _ _ => return numTy α
  | LT.lt α _ _ _ => return numTy α
  | GE.ge α _ _ _ => return numTy α
  | GT.gt α _ _ _ => return numTy α
  | Dvd.dvd α _ _ _ => return numTy α
  | _ => return ty.isConstOf ``False || ty.isConstOf ``True

/-- A `%` inside another `%`: unnormalised wraparound, on which `omega`'s search can blow up. -/
def nestedMod (ty : Lean.Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  let isMod (e : Lean.Expr) := e.isAppOfArity ``HMod.hMod 6
  let inner (e : Lean.Expr) : Bool :=
    (e.appArg!.find? isMod).isSome || ((e.getArg! 4).find? isMod).isSome
  return (ty.find? fun e => isMod e && inner e).isSome

/-- `omega` on a copy of the goal with every non-arithmetic hypothesis cleared (and those with
nested `%`): faster, and immune to `omega` getting lost in unrelated hypotheses. -/
elab "lc_omega" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let mut g := g
    for d in (← getLCtx).decls.toList.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      unless ← isProp d.type do continue
      if (← isArith d.type) && !(← nestedMod d.type) then continue
      try g ← g.clear d.fvarId catch _ => pure ()
    setGoals [g]
    withoutRecover (evalTactic (← `(tactic| omega)))

/-- Discharger for `simp`'s side conditions: arithmetic from the context, else `simp`. -/
elab "lc_disch" : tactic => withoutRecover do
  evalTactic (← `(tactic| first | lc_omega | (simp <;> lc_omega)))

/-- Side goals of the heap lemmas. -/
elab "lc_side" : tactic => withoutRecover do
  evalTactic (← `(tactic| first | with_reducible rfl | lc_omega | (simp <;> lc_omega) | (simp; done)))

/-! ## Inspecting goals -/

def isHPropFact (ty : Lean.Expr) : Bool :=
  ty.isAppOf ``LC.array || ty.isAppOf ``LC.HProp.star

/-- The heap a heap-assertion fact is about. -/
def heapOf? (ty : Lean.Expr) : Option Lean.Expr :=
  if isHPropFact ty then some ty.getAppArgs.back! else none

def exprTerm (e : Lean.Expr) : TacticM Term := do
  let s ← Term.exprToSyntax e
  return s

/-- Store facts in context: `st.get x = …`. -/
def storeFacts : TacticM (Array Term) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some (_, lhs, _) := ty.eq? then
      if lhs.isAppOf ``LC.Store.get then
        out := out.push (← exprTerm d.toExpr)
  return out

/-- Heap facts in context. -/
def heapFacts : TacticM (Array (Lean.Expr × Lean.Expr)) := withMainContext do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if let some hp := heapOf? ty then out := out.push (d.toExpr, hp)
  return out

def mkSimpArgs (extra : Array Term) : TacticM (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) :=
  extra.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)

/-- Run `tac` on the main goal; restore state and return `false` if it fails. -/
def tryTac (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  try withoutRecover tac; return true catch _ => s.restore; return false


/-! ## Heap search -/

/-- Run `k` on goal `g` alone; fail unless it closes `g`. Restores the other goals. -/
def onGoal (g : MVarId) (k : TacticM Unit) : TacticM Unit := do
  let rest ← getGoals
  setGoals [g]
  k
  let left ← (← getGoals).filterM fun g => return !(← g.isAssigned)
  unless left.isEmpty do throwError "lc_auto: goal not closed"
  setGoals rest

/-- Prove the main goal `h a = some ?v` from `pf : H h`, where `H` is a `∗`-tree of arrays. -/
partial def cellFrom (pf : Lean.Expr) : TacticM Unit := withMainContext do
  let ty ← instantiateMVars (← inferType pf)
  let t ← exprTerm pf
  if ty.isAppOf ``LC.array then
    evalTactic (← `(tactic| (refine array_get_at $t ?_ ?_ ?_ <;> lc_side)))
  else if ty.isAppOf ``LC.HProp.star then
    for lem in [``LC.star_get_left, ``LC.star_get_right] do
      let s ← saveState
      try
        evalTactic (← `(tactic| apply $(mkIdent lem) $t))
        let (fvs, g) ← (← getMainGoal).intros
        replaceMainGoal [g]
        cellFrom (mkFVar fvs[1]!)
        return
      catch _ => s.restore
    throwError "lc_auto: cell not owned"
  else throwError "lc_auto: not a heap fact"

/-- Prove the main goal `?H (h.update a v)` from `pf : H h`, choosing `?H`. -/
partial def updFrom (pf : Lean.Expr) : TacticM Unit := withMainContext do
  let ty ← instantiateMVars (← inferType pf)
  let t ← exprTerm pf
  if ty.isAppOf ``LC.array then
    evalTactic (← `(tactic| (refine array_update_at _ $t ?_ ?_ ?_ <;> lc_side)))
  else if ty.isAppOf ``LC.HProp.star then
    for lem in [``LC.star_update_left, ``LC.star_update_right] do
      let s ← saveState
      try
        evalTactic (← `(tactic| apply $(mkIdent lem) $t))
        let (fvs, g) ← (← getMainGoal).intros
        replaceMainGoal [g]
        let hh := mkFVar fvs[1]!
        evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
        let g₁ :: g₂ :: _ ← getGoals | throwError "lc_auto: unexpected goals"
        setGoals [g₁, g₂]
        onGoal g₁ do
          evalTactic (← `(tactic| apply ne_none_of_eq_some))
          cellFrom hh
        onGoal g₂ (updFrom hh)
        return
      catch e =>
        trace[lc_auto] "updFrom {lem}: {e.toMessageData}"
        s.restore
    throwError "lc_auto: cell not owned"
  else throwError "lc_auto: not a heap fact"

/-- Prove the main goal `H' h` from `pf : H h` for `∗`-trees of the same shape. Leftover goals
are equalities of cell lists. -/
partial def heapFrom (pf : Lean.Expr) : TacticM Unit := withMainContext do
  let ty ← instantiateMVars (← inferType pf)
  let tgt ← instantiateMVars (← getMainTarget)
  let t ← exprTerm pf
  if ← tryTac (evalTactic (← `(tactic| exact $t))) then return
  if ty.isAppOf ``LC.HProp.star && tgt.isAppOf ``LC.HProp.star then
    evalTactic (← `(tactic| refine star_mono $t ?_ ?_))
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      let (fvs, g) ← (← getMainGoal).intros
      setGoals [g]
      heapFrom (mkFVar fvs[1]!)
      out := out ++ (← getGoals)
    setGoals out.toList
  else if ty.isAppOf ``LC.array && tgt.isAppOf ``LC.array then
    evalTactic (← `(tactic| refine array_congr $t (by first | rfl | simp) ?_))
    _ ← tryTac (evalTactic (← `(tactic| simp (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat])))
  else throwError "lc_auto: heap shapes differ"

/-! ## The pieces -/

/-- `lhs = some ?v`: compute `lhs` by `simp` and assign `?v`. -/
def evalGoalCore (extras : Array Term) : TacticM Unit := withMainContext do
  let facts ← storeFacts
  let args ← mkSimpArgs (facts ++ extras)
  evalTactic (← `(tactic| focus
    (try (conv => lhs; simp (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat, $args,*]))
    first | done | exact rfl))

def evalGoal (extras : Array Term) : TacticM Unit := withMainContext do
  let hb ← IO.getNumHeartbeats
  trace[lc_auto] "eval: {← getMainTarget}"
  try evalGoalCore extras
  finally trace[lc_auto] "eval done ({((← IO.getNumHeartbeats) - hb) / 1000}k)"

/-- Prove `h a = some ?v` from some heap fact. -/
def cellGoal : TacticM Unit := withMainContext do
  for (pf, _) in ← heapFacts do
    let g ← getMainGoal
    let rest := (← getGoals).tail
    setGoals [g]
    if ← tryTac (cellFrom pf) then
      if (← getGoals).isEmpty then setGoals rest; return
    setGoals (g :: rest)
  throwError "lc_auto: cannot find the cell in any owned array"

/-- After a store to `h.update a v`, turn the heap fact about `h` into one about the new
heap and generalize it. -/
def afterStore : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some upd := tgt.find? (fun e => e.isAppOfArity ``LC.Heap.update 3) | return
  let h := upd.getArg! 0
  for (pf, hp) in ← heapFacts do
    unless ← isDefEq hp h do continue
    let s ← saveState
    try
      let H ← mkFreshExprMVar (mkConst ``LC.HProp)
      let target := mkApp H upd
      let pfNew ← mkFreshExprMVar target
      let gs ← Tactic.run pfNew.mvarId! (withoutRecover (updFrom pf))
      unless gs.isEmpty do throwError "leftover"
      let ty ← instantiateMVars target
      let pfv ← instantiateMVars pfNew
      let (_, g') ← g.note `hheap pfv ty
      replaceMainGoal [g']
      let ut ← exprTerm upd
      evalTactic (← `(tactic| generalize $ut:term = h' at *))
      if let some fv := pf.fvarId? then
        _ ← tryTac (evalTactic (← `(tactic| clear $(← exprTerm (mkFVar fv)))))
      return
    catch e =>
      trace[lc_auto] "afterStore failed: {e.toMessageData}"
      s.restore
  -- no heap fact: leave the goal alone

/-- `a ≤ b` and `b ≤ a` for variables: substitute `a = b`. -/
partial def antisymm (fuel : Nat := 8) : TacticM Unit := withMainContext do
  if fuel = 0 then return
  let mut les : Array (Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``LE.le 4 then
      let a := ty.getArg! 2
      let b := ty.getArg! 3
      if (a.isFVar || b.isFVar) && a != b && (← inferType a).isConstOf ``Nat then
        les := les.push (a, b, d.toExpr)
  for (a, b, p) in les do
    for (a', b', q) in les do
      if a == b' && b == a' then
        let s ← saveState
        try
          let g ← getMainGoal
          let e ← mkAppM ``Nat.le_antisymm #[p, q]
          let (fv, g) ← (← g.assert `hEq (← inferType e) e).intro1
          let g ← (do pure (← substCore g fv (symm := false) (tryToSkip := true)).2) <|>
                   (do pure (← substCore g fv (symm := true) (tryToSkip := true)).2)
          replaceMainGoal [g]
          antisymm (fuel - 1); return
        catch _ => s.restore

/-- Destructure `∧`/`∃` hypotheses (including invariants applied to a store), `subst`
equalities between variables, and normalise evaluated conditions. -/
partial def prep (extras : Array Term) : TacticM Unit := do
  _ ← tryTac (evalTactic (← `(tactic| intros)))
  -- destruct
  let rec loop : Nat → TacticM Unit
    | 0 => pure ()
    | n + 1 => withMainContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        let ty ← instantiateMVars d.type
        if isHPropFact ty then continue
        unless (← isProp ty) do continue
        let ty' ← whnfR ty
        let mut go := ty'.isAppOf ``And || ty'.isAppOf ``Exists
        if !go then
          -- an invariant: an application to a store
          let args := ty.getAppArgs
          let hasStore ← args.anyM fun a => do
            let at_ ← inferType a
            return at_.isConstOf ``LC.Store || at_.isAppOf ``List && (← isDefEq at_ (mkConst ``LC.Store))
          if hasStore && ty.getAppFn.isConst then
            let tyD ← whnfD ty
            go := tyD.isAppOf ``And || tyD.isAppOf ``Exists
        if go then
          let g ← getMainGoal
          let gs ← g.cases d.fvarId
          replaceMainGoal (gs.map (·.mvarId)).toList
          loop n
          return
  loop 64
  _ ← tryTac (evalTactic (← `(tactic| subst_vars)))
  -- normalise evaluated conditions and computed booleans
  withMainContext do
    let facts ← storeFacts
    let args ← mkSimpArgs (facts ++ extras)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let ty ← instantiateMVars d.type
      let some (_, lhs, _) := ty.eq? | continue
      let interesting := lhs.isAppOf ``LC.Expr.eval || (← inferType lhs).isConstOf ``Bool
      unless interesting do continue
      if (← getGoals).isEmpty then return
      let t ← exprTerm d.toExpr
      _ ← tryTac (evalTactic (← `(tactic| simp (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat, $args,*] at $(⟨t⟩):term)))
  if (← getGoals).isEmpty then return
  antisymm

/-- Unfold `f.result`, `f.ret`, `f.body` for a concrete function `f` in the target. -/
def unfoldFnFields : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (pre := fun e => do
    if (e.isAppOfArity ``LC.Fn.result 1 || e.isAppOfArity ``LC.Fn.ret 1) && e.appArg!.isConst then
      return .done (← whnfD e)
    return .continue)
  unless tgt == tgt' do replaceMainGoal [← g.replaceTargetDefEq tgt']

/-- The statement a `swp`/`swpo` goal is about, as a constructor name. -/
def stmtOf (tgt : Lean.Expr) : MetaM (Option (Bool × Name × Lean.Expr)) := do
  let tgt ← whnfR tgt
  let isO := tgt.isAppOfArity ``LC.swpo 5
  unless tgt.isAppOfArity ``LC.swp 5 || isO do return none
  let s ← whnf (tgt.getArg! 1)
  let .const n _ := s.getAppFn | return none
  return some (isO, n, s)

mutual

/-- Process one goal completely: prep, then a statement step or the pure solver. -/
partial def auto (extras : Array Term) : TacticM Unit := do
  trace[lc_auto] "auto: {← getMainTarget}"
  let hb0 ← IO.getNumHeartbeats
  prep extras
  trace[lc_auto] "prepped ({((← IO.getNumHeartbeats) - hb0) / 1000}k)"
  if (← getGoals).isEmpty then return
  unfoldFnFields
  let tgt ← instantiateMVars (← getMainTarget)
  match ← stmtOf tgt with
  | some (isO, n, _) => step extras isO n
  | none => pure_ extras

/-- One symbolic-execution step, then `auto` on what it leaves. -/
partial def step (extras : Array Term) (isO : Bool) (n : Name) : TacticM Unit := do
  let g ← getMainGoal
  let s ← saveState
  let cont (tac : TacticM Unit) : TacticM Unit := do
    try tac
    catch e =>
      trace[lc_auto] "step {n} failed: {e.toMessageData}"
      s.restore; setGoals [g]; throw e
  -- the continuation goals, each processed with `auto`
  let finish : TacticM Unit := do
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      if ← g.isAssigned then continue
      setGoals [g]
      _ ← tryTac (evalTactic (← `(tactic| dsimp only)))
      auto extras
      out := out ++ (← getGoals)
    setGoals out.toList
  let ev : TacticM Unit := evalGoal extras
  trace[lc_auto] "step {n}"
  try stepCore extras isO n cont finish ev
  catch _ => s.restore; setGoals [g]

partial def stepCore (_extras : Array Term) (isO : Bool) (n : Name)
    (cont : TacticM Unit → TacticM Unit) (finish ev : TacticM Unit) : TacticM Unit := do
  match n with
  | ``LC.Stmt.skip =>
    cont do evalTactic (← if isO then `(tactic| apply swpo_skip) else `(tactic| apply swp_skip))
    finish
  | ``LC.Stmt.assign =>
    cont do
      evalTactic (← if isO then `(tactic| apply swpo_assign)
                    else `(tactic| apply swp_assign))
      ev
    finish
  | ``LC.Stmt.seq =>
    cont do evalTactic (← if isO then `(tactic| apply swpo_seq) else `(tactic| apply swp_seq))
    finish
  | ``LC.Stmt.ite =>
    cont do
      evalTactic (← if isO then `(tactic| apply swpo_ite_eval)
                    else `(tactic| apply swp_ite_eval))
      ev
    finish
  | ``LC.Stmt.load =>
    cont do
      evalTactic (← if isO then `(tactic| apply swpo_load)
                    else `(tactic| apply swp_load))
      ev
      cellGoal
      -- `xs[k]!` from the cell lookup becomes `f ys[i]`
      evalTactic (← `(tactic| all_goals try simp (disch := lc_disch) only
        [getElem!_pos, List.getElem_map, Nat.add_sub_cancel_left, List.getElem_cons_zero]))
      evalTactic (← `(tactic| first | rfl | (simp [Val.ty]; done)))
    finish
  | ``LC.Stmt.store =>
    cont do
      evalTactic (← if isO then `(tactic| apply swpo_store)
                    else `(tactic| apply swp_store))
      ev; ev
      evalTactic (← `(tactic| first | rfl | (simp [Val.ty]; done) | simp [Val.ty]))
      cellGoal
      afterStore
    finish
  | ``LC.Stmt.brk =>
    if isO then
      cont do evalTactic (← `(tactic| apply swpo_brk))
      finish
  | ``LC.Stmt.ret =>
    if isO then
      cont do evalTactic (← `(tactic| apply swpo_ret)); ev
      finish
  | _ => pure ()  -- `while` and `call`: needs the user (invariant / callee spec)

/-- A goal with no program left: unfold, instantiate existentials from equations, then
close the leaves with `simp`, `omega` and friends. -/
partial def pure_ (extras : Array Term) : TacticM Unit := do
  trace[lc_auto] "pure: {← getMainTarget}"
  let xargs ← mkSimpArgs extras
  _ ← tryTac (evalTactic (← `(tactic| simp +zetaDelta only [$xargs,*])))
  _ ← tryTac (evalTactic (← `(tactic| dsimp +zetaDelta only)))
  if (← getGoals).isEmpty then return
  -- split ∃ and ∧
  let rec split (g : MVarId) : TacticM (List MVarId) := do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    if ty.isAppOf ``And then
      let gs ← g.apply (mkConst ``And.intro)
      return (← gs.mapM split).flatten
    else if ty.isAppOf ``Exists then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``Exists.intro)
      -- the witness goal comes last
      return (← gs.mapM split).flatten
    else return [g]
  let gs ← split (← getMainGoal)
  -- equations `lhs = rhs[?w]` fix the witnesses
  let mut rest := #[]
  for g in gs do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if let some (_, lhs, rhs) := ty.eq? then
      if rhs.hasExprMVar && !lhs.hasExprMVar then
        setGoals [g]
        if ← tryTac (evalGoal extras) then continue
      if lhs.isMVar && !rhs.hasExprMVar then
        setGoals [g]
        if ← tryTac (evalTactic (← `(tactic| exact rfl))) then continue
    rest := rest.push g
  -- leaves
  let mut out := #[]
  for g in rest do
    if ← g.isAssigned then continue
    setGoals [g]
    leaf extras
    out := out ++ (← getGoals)
  setGoals out.toList

partial def leaf (extras : Array Term) : TacticM Unit := withMainContext do
  let hb ← IO.getNumHeartbeats
  trace[lc_auto] "leaf: {← getMainTarget}"
  leafCore extras
  trace[lc_auto] "leaf done ({((← IO.getNumHeartbeats) - hb) / 1000}k heartbeats, {(← getGoals).length} left)"

partial def leafCore (extras : Array Term) : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  if tgt.hasExprMVar then return
  -- heap assertions
  if isHPropFact tgt then
    for (pf, _) in ← heapFacts do
      if ← tryTac (heapFrom pf) then
        let gs ← getGoals
        let mut out := #[]
        for g in gs do
          if ← g.isAssigned then continue
          setGoals [g]
          leafCore extras
          out := out ++ (← getGoals)
        setGoals out.toList
        return
    return
  if ← tryTac (evalTactic (← `(tactic| first | exact rfl | with_reducible assumption | lc_omega))) then return
  let facts ← storeFacts
  let args ← mkSimpArgs (facts ++ extras)
  let simpAll ← `(tactic| simp +zetaDelta (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat, $args,*])
  let s0 ← saveState
  try
    evalTactic simpAll
    for g in ← getGoals do
      setGoals [g]
      if ← tryTac (evalTactic (← `(tactic| exact rfl))) then continue
      if ← tryTac (evalTactic (← `(tactic| with_reducible assumption))) then continue
      if ← tryTac (evalTactic (← `(tactic| lc_omega))) then continue
      evalTactic (← `(tactic| (intros; lc_omega)))
    setGoals []
    return
  catch _ => s0.restore
  -- `∀ x, A x → B x`: introduce, simplify the new hypotheses, try again
  let s ← saveState
  try
    let (fvs, g) ← (← getMainGoal).intros
    if fvs.isEmpty then throwError "no binders"
    setGoals [g]
    withMainContext do
      for fv in fvs do
        if (← getGoals).isEmpty then break
        let t ← exprTerm (mkFVar fv)
        _ ← tryTac (evalTactic (← `(tactic| simp (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat] at $(⟨t⟩):term)))
    if (← getGoals).isEmpty then return
    evalTactic (← `(tactic| first | with_reducible assumption | lc_omega | (simp (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat] <;> lc_omega)))
    return
  catch _ => s.restore
  if ← tryTac (evalTactic (← `(tactic| set_option maxHeartbeats 40000 in grind))) then return
  -- partial progress is still progress
  _ ← tryTac (evalTactic (← `(tactic|
      simp +zetaDelta (disch := lc_disch) [lc_simp, -BitVec.ofNat_toNat, $args,*])))
  -- a conjunction that `simp` exposed: work on the parts separately
  if (← getGoals).length == 1 then
    let g ← getMainGoal
    if (← whnfR (← instantiateMVars (← g.getType))).isAppOf ``And then
      let gs ← g.apply (mkConst ``And.intro)
      let mut out := #[]
      for g in gs do
        setGoals [g]
        leafCore extras
        out := out ++ (← getGoals)
      setGoals out.toList

end

end LC.Auto

open LC.Auto in
/-- `lc_auto` runs the routine part of an LC proof: it symbolically executes the statement
(assignments, loads, stores, `if`, `break`, `return`), carries store facts across
assignments, finds and updates the cells owned by `array`s inside `∗`, and closes the
resulting pure goals with `simp`, `omega` and `grind`. It stops at `while` (use `lc_while`)
and `call`; whatever it can't close is left for you.

`lc_auto [foo, bar]` also unfolds or rewrites with `foo` and `bar` (your invariants, variants
and spec lemmas). -/
syntax (name := lcAuto) "lc_auto" (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| lc_auto $[[$ts,*]]?) => do
    let extras : Array Term := match ts with | some ts => ts.getElems | none => #[]
    let gs ← getGoals
    let mut out := #[]
    for g in gs do
      setGoals [g]
      withoutRecover (LC.Auto.auto extras)
      out := out ++ (← getGoals)
    setGoals out.toList

/-- `lc_while I μ [extras]` applies the loop rule with invariant `I` and variant `μ`, then runs
`lc_auto [extras]` on the four obligations (condition defined, body, exit, entry). -/
syntax (name := lcWhile) "lc_while " term:max term:max (" [" term,* "]")? : tactic

/-- Focus the first goal that is a `swp`/`swpo` about statement kind `n`. -/
def LC.Auto.focusStmt (n : Name) : TacticM (MVarId × List MVarId) := do
  let gs ← getGoals
  for g in gs do
    let tgt ← instantiateMVars (← g.getType)
    if let some (_, n', _) ← g.withContext (LC.Auto.stmtOf tgt) then
      if n' == n then return (g, gs.filter (· != g))
  throwError "no goal is about a {n}"

elab_rules : tactic
  | `(tactic| lc_while $I $μ $[[$ts,*]]?) => do
    let ts : Array Term := match ts with | some ts => ts.getElems | none => #[]
    let (g, rest) ← LC.Auto.focusStmt ``LC.Stmt.while
    setGoals [g]
    evalTactic (← `(tactic| (first
        | refine LC.swpo_while $I $μ ?_ ?_ ?_ _ _ ?_
        | refine LC.swp_while $I $μ ?_ ?_ ?_ _ _ ?_) <;> lc_auto [$ts,*]))
    setGoals ((← getGoals) ++ rest)

/-- `lc_call hfind spec init [extras]` steps over `x = f(args);` for a callee that owns no memory.
`hfind : P.find? "f" = some g` and `spec` is the callee's body proof (an instance of its
spec theorem, in the shape `swpo_call_pure` wants). Then `lc_auto [extras]` continues.
`init` proves `g.initStore … = some …`; pass `_` to have it computed. -/
syntax (name := lcCall) "lc_call " term:max term:max term:max (" [" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| lc_call $hP $spec $init $[[$ts,*]]?) => do
    let extras : Array Term := match ts with | some ts => ts.getElems | none => #[]
    let (g, others) ← LC.Auto.focusStmt ``LC.Stmt.call
    setGoals [g]
    evalTactic (← `(tactic| apply LC.swpo_call_pure $hP))
    let gs ← getGoals
    let some hargs := gs[0]? | throwError "lc_call: unexpected goals"
    let some hinit := gs[1]? | throwError "lc_call: unexpected goals"
    let some hbody := gs[2]? | throwError "lc_call: unexpected goals"
    let some hq := gs[3]? | throwError "lc_call: unexpected goals"
    LC.Auto.onGoal hargs (LC.Auto.evalGoal extras)
    LC.Auto.onGoal hinit (if init.raw.isOfKind ``Lean.Parser.Term.hole then do
        evalTactic (← `(tactic|
          first | rfl | (simp [Fn.initStore, Store.empty, lc_simp] <;> rfl)))
      else do evalTactic (← `(tactic| exact $init)))
    LC.Auto.onGoal hbody (evalTactic (← `(tactic| exact $spec)))
    setGoals [hq]
    withoutRecover (LC.Auto.auto extras)
    setGoals ((← getGoals) ++ others)
