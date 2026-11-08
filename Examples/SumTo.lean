import LC

/-!
# `sum_to`: a first loop, run and proved

The program, a few interpreter runs turned into theorems (`Fn.call_sound` makes the
interpreter a proof generator), and the full Hoare-logic proof that `sum_to(n)` returns
exactly n(n+1)/2 for every 32-bit `n`. See docs/hoare-logic.md.
-/

open LC

namespace Examples.SumTo

/-! ## The program

```c
uint64_t sum_to(uint32_t n) {
  uint32_t i = 0; uint64_t s = 0;
  while (i < n) { i = i + 1; s = s + (uint64_t)i; }
  return s;
}
```
-/
def sumTo : Fn where
  name   := "sum_to"
  params := [("n", .int .u32)]
  locals := [("i", .int .u32), ("s", .int .u64)]
  body   := .block [
    "i" ::= .u32 0,
    "s" ::= .u64 0,
    .while (v "i" <. v "n") (.block [
      "i" ::= v "i" + .u32 1,
      "s" ::= v "s" + .cast .u64 (v "i")
    ])
  ]
  ret    := .int .u64
  result := v "s"

#guard sumTo.typeCheck
#eval sumTo.call [.u32 10]                       -- ok 55u64
#guard sumTo.call [.u32 10] = .ok (.u64 55)
#guard sumTo.call [.u32 100000] (fuel := 1000000) = .ok (.u64 5000050000)  -- beyond 2³²: the u64 accumulator matters

/-- A theorem about the *semantics*, not the interpreter: `sum_to(10)` returns 55.
`decide` makes the kernel evaluate the interpreter; `call_sound` turns that into
an `Exec` derivation. No `native_decide`, so the compiler is not trusted. -/
theorem sumTo_10 : ∃ m', sumTo.Returns [.u32 10] [] (.u64 55) m' :=
  Fn.call_sound (fuel := 100) (by decide)

/-- The triangular numbers: the mathematical specification. -/
def tri (k : Nat) : Nat := k * (k + 1) / 2

theorem tri_succ (k : Nat) : tri (k + 1) = tri k + (k + 1) := by
  unfold tri
  have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by grind
  omega

/-- Loop invariant: the store holds `n`, a counter `i ≤ n`, and `s = tri i`.
Stating the *whole* store exactly is heavy-handed but very predictable; the separation-logic
examples state only what they need. -/
def sumToInv (n : Nat) (m : Mem) : Assertion := fun σ =>
  ∃ i, i ≤ n ∧ σ = ⟨[("n", nu32 n), ("i", nu32 i), ("s", nu64 (tri i))], m⟩

/-- Loop variant: `n - i` (iterations remaining). -/
def sumToVar (n : Nat) : State → Nat := fun σ =>
  match σ.st.get "i" with
  | some (.int _ bv) => n - bv.toNat
  | _ => 0

/-- **`sum_to(n)` returns `n(n+1)/2` for every `n : u32`, with no UB and termination.**

The proof is one symbolic-execution pass:
1. `suffices`: reduce `Fn.Returns` to a `wp` of the body (`Fn.returns_of_wp`).
2. `simp only [wp_seq, wp_assign]` executes the two initialising assignments.
3. `wp_while` with invariant `sumToInv n` and variant `sumToVar n` leaves four goals:
   `init`, `cond` (the guard never has UB), `body` (preserve and decrease), and `exit`.
4. Each goal is `simp` with the `LC/Logic/Eval.lean` lemmas, then a little arithmetic.
-/
theorem sumTo_correct (n : Nat) (hn : n < 2 ^ 32) (m : Mem) :
    sumTo.Returns [.u32 n] m (.u64 (tri n)) m := by
  suffices key : wp sumTo.body (fun σ => ∃ v, sumTo.result.eval σ.st = some v ∧
      v.ty = sumTo.ret ∧ (v = .u64 (tri n) ∧ σ.mem = m)) ⟨[("n", nu32 n)], m⟩ by
    obtain ⟨v, m', hv, rfl, rfl⟩ := Fn.returns_of_wp (f := sumTo) (args := [.u32 n])
      (st₀ := [("n", nu32 n)]) (m := m)
      (post := fun v m' => v = .u64 (tri n) ∧ m' = m) (by simp [Fn.initStore, sumTo, Store.empty]; rfl) key
    exact hv
  simp only [sumTo, Stmt.block, wp_seq, wp_assign]
  refine ⟨_, rfl, _, rfl, ?_⟩
  have hn32 : n % 2 ^ 32 = n := Nat.mod_eq_of_lt hn
  refine wp_while (sumToInv n m) (sumToVar n) ?cond ?body ?exit _ ⟨0, by omega, ?init⟩
  case init => simp [tri]; constructor <;> rfl
  case cond =>
    rintro σ ⟨i, hi, rfl⟩
    simp [intBinOp]
  case body =>
    rintro σ ⟨i, hi, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    -- the guard was true, so i < n
    simp [nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    -- execute `i = i + 1; s = s + (uint64_t)i`
    simp [nu32, nu64, intBinOp, Expr.u32, Val.u32, Val.ofInt, sumToInv, sumToVar, hi32]
    -- Pure arithmetic remains: the new counter is `i+1` (no u32 wrap, since
    -- i < n < 2³²), the new sum is `tri (i+1)`, and the variant decreased.
    have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : ((i : Int) + 1) % 4294967296 = ((i + 1 : Nat) : Int) := by omega
    rw [h1, h2, BitVec.ofInt_natCast]
    refine ⟨⟨i + 1, by omega, ?_, ?_⟩, by omega⟩
    · exact BitVec.ofNat_add_ofNat i 1
    · rw [BitVec.ofNat_add_ofNat, tri_succ]
  case exit =>
    rintro σ ⟨i, hi, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    -- the guard was false, so i = n
    simp [nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    obtain rfl : i = n := by omega
    simp; constructor <;> rfl

/-! ## Reading the spec carefully

`.u64 (tri n)` is `tri n` *mod 2⁶⁴*. Unsigned arithmetic wraps, so a spec stated
as a bit-vector could quietly be a statement about the wrapped value. Here it isn't,
because `tri n < 2⁶⁴` whenever `n < 2³²`. This corollary says the returned number
is **exactly** n(n+1)/2. -/

theorem tri_lt (n : Nat) (hn : n < 2 ^ 32) : tri n < 2 ^ 64 := by
  have : n * (n + 1) ≤ (2 ^ 32 - 1) * 2 ^ 32 := Nat.mul_le_mul (by omega) (by omega)
  have := Nat.div_le_self (n * (n + 1)) 2
  unfold tri; omega

theorem sumTo_exact (n : Nat) (hn : n < 2 ^ 32) (m : Mem) :
    ∃ bv : BitVec 64, sumTo.Returns [.u32 n] m (.int .u64 bv) m ∧ bv.toNat = n * (n + 1) / 2 := by
  refine ⟨BitVec.ofNat 64 (tri n), by simpa using sumTo_correct n hn m, ?_⟩
  have := tri_lt n hn
  simp only [BitVec.toNat_ofNat, tri] at this ⊢
  exact Nat.mod_eq_of_lt this

/-- And the payoff from the interpreter theorems: the interpreter can never report UB on `sum_to`. -/
theorem sumTo_no_ub (n : Nat) (hn : n < 2 ^ 32) (m : Mem) (fuel : Nat) :
    ∀ st₀, sumTo.initStore [.u32 n] = some st₀ → run fuel ⟨st₀, m⟩ sumTo.body ≠ .stuck := by
  intro st₀ h₀
  obtain ⟨st₀', st₁, h₀', hex, -⟩ := sumTo_correct n hn m
  rw [h₀] at h₀'; cases h₀'
  intro hrun
  exact run_stuck_sound hrun _ hex


end Examples.SumTo
