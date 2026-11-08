/-
Milestone 1 exercises. Each one takes 15 minutes or less.
Run:  lake env lean exercises/core/M1_Exercises.lean
(Use `lake env` so the file can `import LC`. Run `lake build` once first.)

Read docs/m1-walkthrough.md first. Solutions: exercises/solutions/M1_Exercises.lean.
-/
import LC
open LC

/-! ## M1.1 (🔧 10 min): write a program
Integer square root: return the largest `r` with `r*r ≤ n`, for `n : u32`.
Use a `u64` accumulator so `(r+1)*(r+1)` cannot wrap, and convert back with `.cast .u32`.
Copy the shape of `Examples.M1.sumTo`. -/
def isqrt : Fn where
  name := "isqrt"; params := [("n", .int .u32)]; locals := [("r", .int .u64)]
  body := .skip          -- TODO
  ret := .int .u32
  result := .u32 0       -- TODO

-- Uncomment once written:
-- #guard isqrt.typeCheck
-- #guard isqrt.call [.u32 15] = .ok (.u32 3)
-- #guard isqrt.call [.u32 16] = .ok (.u32 4)
-- #guard isqrt.call [.u32 4294967295] (fuel := 1000000) = .ok (.u32 65535)

/-! ## M1.2 (🔧 10 min): a bug that isn't UB
Here is the "obvious" version, all in `u32`. Find an input where it goes wrong, then
explain in a comment why our UB-detecting semantics does *not* flag it.
Use a small fuel (≈ 200000) when experimenting! -/
def isqrtBad : Fn where
  name := "isqrt_bad"; params := [("n", .int .u32)]; locals := [("r", .int .u32)]
  body := .block [
    "r" ::= .u32 0,
    .while ((v "r" + .u32 1) * (v "r" + .u32 1) <=. v "n") ("r" ::= v "r" + .u32 1)
  ]
  ret := .int .u32
  result := v "r"

-- #eval isqrtBad.call [.u32 ???] (fuel := 200000)

/-! ## M1.3 (🔧 10 min): a program equivalence by inversion
Hint: `constructor`; in one direction `cases h`, and look at what each rule demands. -/
theorem while_false_iff (σ σ' : State) (s : Stmt) :
    Exec σ (.while (.lit (.bool false)) s) σ' ↔ σ' = σ := by
  sorry

/-! ## M1.4 (🔧 5 min) -/
theorem skip_seq_iff (σ σ' : State) (s : Stmt) :
    Exec σ (.seq .skip s) σ' ↔ Exec σ s σ' := by
  sorry

/-! ## M1.5 (🔧 15 min): more fuel never hurts
Hint: induction on `n` generalizing `m σ σ' s`. In the `succ` case, write `m` as `k + 1`,
then follow the structure of `run_sound` in LC/Interp.lean. -/
theorem run_mono {n m : Nat} {σ σ' : State} {s : Stmt} (hle : n ≤ m) :
    run n σ s = .ok σ' → run m σ s = .ok σ' := by
  sorry

/-! ## M1.6 (🔧 15 min, stretch): the interpreter is complete
Every terminating execution is found with enough fuel. Hint: induction on `h`; for
`seq` and `whileTrue`, use `max n₁ n₂ + 1` fuel and `run_mono` (pass `(m := …)` explicitly). -/
theorem run_complete {σ σ' : State} {s : Stmt} (h : Exec σ s σ') :
    ∃ n, run n σ s = .ok σ' := by
  sorry

/-! ## M1.7 (✍️ 5 min)
`run_stuck_sound` (LC/Interp.lean) uses `Exec.det`. In which cases, and why would the
theorem be false for a non-deterministic language? Answer in a comment. -/

/-! ## M1.8 (🔧 10 min): an experiment, then undo it
In LC/Semantics.lean, temporarily make `land` strict: delete its special case so it
falls through to `evalBinOp` (and add `| .land => ...` handling there, or let it be `none`).
Run `lake build`. Which `#guard` in Examples/M1.lean breaks, and what does that tell you about
the C our printer must emit for `&&`? Then undo the change. -/
