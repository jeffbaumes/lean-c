import LC.Logic.Sep

/-!
# Helpers for writing specifications

Specs talk about mathematical numbers and lists; programs manipulate `BitVec`-carrying
`Val`s. These abbreviations and lemmas bridge the two.
-/

namespace LC

/-- Naturals as LC values. -/
abbrev nu32 (k : Nat) : Val := .int .u32 (BitVec.ofNat 32 k)
abbrev nu64 (k : Nat) : Val := .int .u64 (BitVec.ofNat 64 k)

@[simp] theorem u32_eq (k : Nat) : Val.u32 (k : Int) = nu32 k := by
  simp [Val.u32, Val.ofInt, BitVec.ofInt_natCast]
@[simp] theorem u64_eq (k : Nat) : Val.u64 (k : Int) = nu64 k := by
  simp [Val.u64, Val.ofInt, BitVec.ofInt_natCast]

/-- Lists of words/bytes as LC cell values. -/
abbrev u32s (xs : List (BitVec 32)) : List Val := xs.map (Val.int .u32)
abbrev u8s (xs : List (BitVec 8)) : List Val := xs.map (Val.int .u8)

/-- `a - b` on bit-vectors is exact when it can't underflow. -/
theorem bv_sub {w a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ w) :
    BitVec.ofNat w a - BitVec.ofNat w b = BitVec.ofNat w (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : b < 2 ^ w), Nat.mod_eq_of_lt ha]
  have : 2 ^ w - b + a = (a - b) + 2 ^ w := by omega
  rw [this, Nat.add_mod_right]

/-- The usual loop variant `n - i`, reading the counter from local `"i"`. -/
def counterVariant (n : Nat) : Store → Heap → Nat := fun st _ =>
  match st.get "i" with
  | some (.int _ bv) => n - bv.toNat
  | _ => 0

end LC
