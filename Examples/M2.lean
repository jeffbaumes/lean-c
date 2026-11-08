import LC
import Examples.M1

/-!
# Milestone 2: `sum_to` is correct for every input
-/

open LC Examples.M1

namespace Examples.M2

/-- Naturals as LC values. A spec talks about mathematical numbers; these
convert them into `BitVec`-carrying values. -/
abbrev nu32 (k : Nat) : Val := .int .u32 (BitVec.ofNat 32 k)
abbrev nu64 (k : Nat) : Val := .int .u64 (BitVec.ofNat 64 k)

@[simp] theorem u32_eq (k : Nat) : Val.u32 (k : Int) = nu32 k := by
  simp [Val.u32, Val.ofInt, BitVec.ofInt_natCast]
@[simp] theorem u64_eq (k : Nat) : Val.u64 (k : Int) = nu64 k := by
  simp [Val.u64, Val.ofInt, BitVec.ofInt_natCast]

/-- The triangular numbers: the mathematical specification. -/
def tri (k : Nat) : Nat := k * (k + 1) / 2

theorem tri_succ (k : Nat) : tri (k + 1) = tri k + (k + 1) := by
  unfold tri
  have : (k + 1) * (k + 1 + 1) = k * (k + 1) + 2 * (k + 1) := by grind
  omega

/-- Loop invariant: the store holds `n`, a counter `i ≤ n`, and `s = tri i`.
Stating the *whole* store exactly is heavy-handed but very predictable; M3's
separation logic will let us say only what we need. -/
def inv (n : Nat) (m : Mem) : Assertion := fun σ =>
  ∃ i, i ≤ n ∧ σ = ⟨[("n", nu32 n), ("i", nu32 i), ("s", nu64 (tri i))], m⟩

/-- Loop variant: `n - i` (iterations remaining). -/
def var (n : Nat) : State → Nat := fun σ =>
  match σ.st.get "i" with
  | some (.int _ bv) => n - bv.toNat
  | _ => 0

/-- **`sum_to(n)` returns `n(n+1)/2` for every `n : u32`, with no UB and termination.**

The proof is one symbolic-execution pass:
1. `suffices`: reduce `Fn.Returns` to a `wp` of the body (`Fn.returns_of_wp`).
2. `simp only [wp_seq, wp_assign]` executes the two initialising assignments.
3. `wp_while` with invariant `inv n` and variant `var n` leaves four goals:
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
  refine wp_while (inv n m) (var n) ?cond ?body ?exit _ ⟨0, by omega, ?init⟩
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
    simp [nu32, nu64, intBinOp, Expr.u32, Val.u32, Val.ofInt, inv, var, hi32]
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

/-- And the payoff from M1's interpreter theorems: the interpreter can never report UB on `sum_to`. -/
theorem sumTo_no_ub (n : Nat) (hn : n < 2 ^ 32) (m : Mem) (fuel : Nat) :
    ∀ st₀, sumTo.initStore [.u32 n] = some st₀ → run fuel ⟨st₀, m⟩ sumTo.body ≠ .stuck := by
  intro st₀ h₀
  obtain ⟨st₀', st₁, h₀', hex, -⟩ := sumTo_correct n hn m
  rw [h₀] at h₀'; cases h₀'
  intro hrun
  exact run_stuck_sound hrun _ hex

end Examples.M2
