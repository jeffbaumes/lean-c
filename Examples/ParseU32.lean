import LC

/-!
# Parsing a decimal `uint32_t`, with a verified helper call

```c
bool is_digit(uint8_t c);                                   // '0' ≤ c ≤ '9'
bool parse_u32(uint8_t *p, uint32_t n, uint32_t *out);      // false on bad input or overflow
```

`parse_u32` **calls** `is_digit`, using `is_digit`'s *specification* rather than its code
(`swpo_call_pure`). It **returns early** on the first non-digit, and on overflow. Overflow is
detected *before* it happens: `acc > (UINT32_MAX - d) / 10` is exactly "`acc * 10 + d` won't fit".
The result is written through `out` only on success.
-/

open LC

namespace Examples.ParseU32

def isDigit : Fn where
  name   := "is_digit"
  params := [("c", .int .u8)]
  locals := []
  body   := .skip
  ret    := .bool
  result := .u8 48 <=. v "c" &&. v "c" <=. .u8 57

def parseU32 : Fn where
  name   := "parse_u32"
  params := [("p", .ptr .u8), ("n", .int .u32), ("out", .ptr .u32)]
  locals := [("i", .int .u32), ("acc", .int .u32), ("c", .int .u8), ("ok", .bool), ("d", .int .u32)]
  body   := .block [
    .ite (v "n" ==. .u32 0) (.ret .ff) .skip,
    "i" ::= .u32 0,
    "acc" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "c" (v "p") (v "i"),
      .call (some "ok") "is_digit" [v "c"],
      .ite (!. (v "ok")) (.ret .ff) .skip,
      "d" ::= .cast .u32 (v "c") - .u32 48,
      .ite (v "acc" >. (.u32 4294967295 - v "d") / .u32 10) (.ret .ff) .skip,
      "acc" ::= v "acc" * .u32 10 + v "d",
      "i" ::= v "i" + .u32 1
    ]),
    .store (v "out") (.u32 0) (v "acc"),
    .ret .tt
  ]
  ret    := .bool
  result := .ff

/-- The program both functions live in. -/
def prog : Program := [isDigit, parseU32]

#guard isDigit.typeCheck prog && parseU32.typeCheck prog
#guard (cTranslationUnit prog).isOk

/-- Parse the ASCII string `s` (block 0) into block 1. -/
def runParse (s : String) : Result (Val × Mem) :=
  let bytes := s.toList.map fun c => Val.u8 c.toNat
  parseU32.callMem [.ptr .u8 ⟨0, 0⟩, .u32 bytes.length, .ptr .u32 ⟨1, 0⟩]
    [(0, if bytes.isEmpty then [Val.u8 0] else bytes), (1, [.u32 0])] (P := prog)

def outOf : Result (Val × Mem) → Option Val
  | .ok (.bool true, m) => m.read 1 0
  | _ => none

#guard outOf (runParse "0") = some (.u32 0)
#guard outOf (runParse "1234") = some (.u32 1234)
#guard outOf (runParse "4294967295") = some (.u32 4294967295)      -- UINT32_MAX
#guard outOf (runParse "4294967296") = none                         -- overflow
#guard outOf (runParse "99999999999") = none                        -- overflow, earlier
#guard outOf (runParse "12a4") = none                               -- not a digit
#guard outOf (runParse "") = none                                   -- empty

/-! ## The specification -/

def IsDigit (c : BitVec 8) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

instance (c : BitVec 8) : Decidable (IsDigit c) := by unfold IsDigit; infer_instance

/-- The value of a string of decimal digits, as an unbounded natural number. -/
def decVal (cs : List (BitVec 8)) : Nat := cs.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- What `parse_u32(p, n, out)` promises, for the bytes `cs` at `p`: it succeeds, writing
`decVal cs` to `out[0]`, **exactly when** `cs` is a non-empty string of digits whose value fits
in 32 bits. Otherwise it returns false and changes nothing. -/
def ParseOk (cs : List (BitVec 8)) : Prop :=
  cs ≠ [] ∧ (∀ c ∈ cs, IsDigit c) ∧ decVal cs < 2 ^ 32

/-! ## `is_digit` is correct

This is the theorem `parse_u32`'s proof uses at the call site, instead of `is_digit`'s code. -/

theorem isDigit_spec (P : Program) (c : BitVec 8) :
    swpo P isDigit.body (fun o st h' => ∃ v, isDigit.finish o st = some v ∧
      v = .bool (decide (IsDigit c)) ∧ h' = Heap.empty) [("c", .int .u8 c)] Heap.empty := by
  apply swpo_of_swp; apply swp_skip
  refine ⟨.bool (decide (IsDigit c)), ?_, rfl, rfl⟩
  simp only [Fn.finish, isDigit]
  by_cases h1 : 48 ≤ c.toNat <;> by_cases h2 : c.toNat ≤ 57 <;>
    simp [Expr.eval, intBinOp, BitVec.ule, Expr.u8, Val.u8, Val.ofInt, h1, h2, Val.ty, IsDigit]

theorem isDigit_init (c : BitVec 8) : isDigit.initStore [.int .u8 c] = some [("c", .int .u8 c)] := by
  simp [Fn.initStore, isDigit, Store.empty]; rfl


/-! ## Facts about `decVal` -/

theorem decVal_take_succ (cs : List (BitVec 8)) (i : Nat) (hi : i < cs.length) :
    decVal (cs.take (i + 1)) = decVal (cs.take i) * 10 + (cs[i].toNat - 48) := by
  unfold decVal; rw [List.take_succ_eq_append_getElem hi, List.foldl_append]; rfl

theorem foldl_digits_ge (a : Nat) (ys : List (BitVec 8)) :
    a ≤ ys.foldl (fun acc c => acc * 10 + (c.toNat - 48)) a := by
  induction ys generalizing a with
  | nil => exact Nat.le_refl a
  | cons y ys ih => exact Nat.le_trans (by omega) (ih (a * 10 + (y.toNat - 48)))

/-- Appending digits never makes the value smaller, so an overflowing prefix means the
whole string overflows. -/
theorem decVal_take_le (cs : List (BitVec 8)) (i : Nat) : decVal (cs.take i) ≤ decVal cs := by
  conv => rhs; rw [← List.take_append_drop i cs]
  unfold decVal; rw [List.foldl_append]; exact foldl_digits_ge _ _

/-! ## `parse_u32` is correct -/

def parseInv (p o : Ptr) (cs : List (BitVec 8)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ cs.length ∧ st.get "p" = some (.ptr .u8 p) ∧ st.get "n" = some (nu32 cs.length) ∧
    st.get "out" = some (.ptr .u32 o) ∧ st.get "i" = some (nu32 i) ∧
    st.get "acc" = some (nu32 (decVal (cs.take i))) ∧ decVal (cs.take i) < 2 ^ 32 ∧
    (∀ j c, j < i → cs[j]? = some c → IsDigit c) ∧ h = h₀

/-- **`parse_u32` is correct.** It returns `true` and writes `decVal cs` to `out[0]` exactly when
`ParseOk cs`; otherwise it returns `false` and leaves memory alone. Holds in any program that
contains the real `is_digit`, inside any surrounding memory. -/
theorem parseU32_correct (P : Program) (hP : P.find? "is_digit" = some isDigit)
    (p o : Ptr) (cs : List (BitVec 8)) (w : Val) (hlen : cs.length < 2 ^ 32)
    (h hf : Heap) (m : Mem) (hpre : (array p (u8s cs) ∗ array o [w]) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', parseU32.Returns P [.ptr .u8 p, .u32 cs.length, .ptr .u32 o] m v m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      ((ParseOk cs ∧ v = .bool true ∧ (array p (u8s cs) ∗ array o [nu32 (decVal cs)]) h') ∨
       (¬ ParseOk cs ∧ v = .bool false ∧ h' = h)) := by
  have hinit : parseU32.initStore [.ptr .u8 p, .u32 cs.length, .ptr .u32 o] =
      some [("p", .ptr .u8 p), ("n", nu32 cs.length), ("out", .ptr .u32 o)] := by
    simp [Fn.initStore, parseU32, Store.empty]; repeat' constructor
  refine Fn.returns_of_swpo hinit ?_ d hm
  have hn32 : cs.length % 2 ^ 32 = cs.length := Nat.mod_eq_of_lt hlen
  simp only [parseU32, Stmt.block]
  apply swpo_seq; apply swpo_ite
  by_cases hn0 : cs.length = 0
  · -- empty input: return false immediately
    left
    refine ⟨by simp [nu32, intBinOp, hn0, Expr.u32, Val.u32, Val.ofInt], swpo_ret rfl ?_⟩
    refine ⟨.bool false, rfl, .inr ⟨fun ⟨hne, _⟩ => hne (List.eq_nil_of_length_eq_zero hn0), rfl, rfl⟩⟩
  right
  have hne0 : BitVec.ofNat 32 cs.length ≠ 0#32 := fun e => hn0 (by
    have := congrArg BitVec.toNat e; simpa [hn32] using this)
  refine ⟨by simp [nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt, hne0], swpo_of_swp (swp_skip ?_)⟩
  apply swpo_seq_normal; apply swp_assign rfl
  apply swpo_seq_normal; apply swp_assign rfl
  apply swpo_seq
  refine swpo_while (parseInv p o cs h) (counterVariant cs.length) ?cond ?step ?exit _ _
    ⟨0, by omega, by simp, by simp, by simp, by simp; rfl, by simp [decVal]; rfl, by simp [decVal],
     fun _ _ hj => absurd hj (Nat.not_lt_zero _), rfl⟩
  case cond =>
    rintro st _ ⟨i, -, -, hn, -, hi', -⟩
    simp [hi', hn, intBinOp]
  case exit =>
    -- every byte was a digit and nothing overflowed: write out[0] and return true
    rintro st _ ⟨i, hi, hp, hn, ho, hi', hacc, hfit, hdig, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    obtain rfl : i = cs.length := by omega
    simp only [List.take_length] at hacc hfit
    have hocell := star_get_right hpre fun _ ha => array_get ha (k := 0) (by simp)
    have hpost := star_update_right (v := nu32 (decVal cs)) hpre fun _ ha =>
      ⟨array_ne_none ha (k := 0) (by simp), array_update ha (k := 0) (by simp) _⟩
    simp only [List.set_cons_zero, Nat.add_zero] at hpost hocell
    apply swpo_seq_normal; apply swp_store'
    refine ⟨.u32, o.blk, o.off, by simp [Expr.evalAddr, ho, Expr.u32, Val.u32, Val.ofInt],
      nu32 (decVal cs), by simp [hacc], rfl, ⟨_, hocell⟩, ?_⟩
    refine swpo_ret rfl ⟨.bool true, rfl, .inl ⟨⟨fun e => hn0 (by simp [e]), ?_, hfit⟩, rfl, hpost⟩⟩
    intro c hcmem
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcmem
    exact hdig j _ hj (List.getElem?_eq_getElem hj)
  case step =>
    rintro st _ ⟨i, hi, hp, hn, ho, hi', hacc, hfit, hdig, rfl⟩ hc
    have hi32 : i % 2 ^ 32 = i := Nat.mod_eq_of_lt (by omega)
    simp [hi', hn, nu32, intBinOp, BitVec.ult, hi32, hn32] at hc
    -- c = p[i]
    have hcell := star_get_left hpre fun _ ha => array_get ha (k := i) (by simpa using hc)
    simp only [List.getElem_map] at hcell
    apply swpo_seq_normal; apply swp_load'
    refine ⟨.u8, p.blk, p.off + i, by simp [Expr.evalAddr, hp, hi', nu32, hi32], _, hcell, rfl, ?_⟩
    -- ok = is_digit(c), by is_digit's *specification*
    apply swpo_seq
    refine swpo_call_pure hP (by simp [Expr.evalList]) (isDigit_init cs[i]) (isDigit_spec P cs[i])
      fun v hv => ?_
    subst hv
    simp only [Store.setOpt]
    apply swpo_seq; apply swpo_ite
    by_cases hd : ¬ IsDigit cs[i]
    · -- not a digit: return false
      left
      refine ⟨by simp [hd, evalUnOp], swpo_ret rfl ⟨.bool false, rfl, .inr ⟨fun ⟨_, hall, _⟩ =>
        hd (hall _ (List.getElem_mem hc)), rfl, rfl⟩⟩⟩
    right
    simp only [Classical.not_not] at hd
    refine ⟨by simp [hd, evalUnOp], swpo_of_swp (swp_skip ?_)⟩
    obtain ⟨hd1, hd2⟩ := hd
    have hc8 := cs[i].isLt
    -- d = c - '0'
    apply swpo_seq_normal
    apply swp_assign (v := nu32 (cs[i].toNat - 48))
    · simp [Expr.u32, Val.u32, Val.ofInt, intBinOp]
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_sub, BitVec.toNat_setWidth]
      omega
    -- overflow check: acc > (UINT32_MAX - d) / 10  ⟺  acc * 10 + d > UINT32_MAX
    have hstep := decVal_take_succ cs i hc
    have hwhole := decVal_take_le cs (i + 1)
    generalize hA : decVal (cs.take i) = a at hacc hfit hstep
    generalize hD : cs[i].toNat - 48 = dg at hstep ⊢
    have hdg9 : dg ≤ 9 := by omega
    have hlim : (4294967295 - dg) / 10 < 2 ^ 32 := by omega
    apply swpo_seq; apply swpo_ite
    by_cases hov : (4294967295 - dg) / 10 < a
    · -- would overflow: return false (and so does the whole string)
      left
      refine ⟨?_, swpo_ret rfl ⟨.bool false, rfl, .inr ⟨fun ⟨_, _, hfit'⟩ => ?_, rfl, rfl⟩⟩⟩
      · simp [hacc, nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt, BitVec.ult,
          bv_sub (by omega : dg ≤ 4294967295) (by omega : 4294967295 < 2 ^ 32),
          bv_udiv (by omega : 4294967295 - dg < 2 ^ 32) (by omega : 10 < 2 ^ 32),
          Nat.mod_eq_of_lt hlim, Nat.mod_eq_of_lt hfit, hov]
      · omega
    right
    refine ⟨?_, swpo_of_swp (swp_skip ?_)⟩
    · simp [hacc, nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt, BitVec.ult,
        bv_sub (by omega : dg ≤ 4294967295) (by omega : 4294967295 < 2 ^ 32),
        bv_udiv (by omega : 4294967295 - dg < 2 ^ 32) (by omega : 10 < 2 ^ 32),
        Nat.mod_eq_of_lt hlim, Nat.mod_eq_of_lt hfit, hov]
    -- acc = acc * 10 + d, which now provably fits
    have hnew : a * 10 + dg < 2 ^ 32 := by omega
    apply swpo_seq_normal
    apply swp_assign (v := nu32 (a * 10 + dg))
    · simp [hacc, nu32, intBinOp, Expr.u32, Val.u32, Val.ofInt, bv_mul, BitVec.ofNat_add_ofNat]
    apply swpo_of_swp; apply swp_assign'
    simp [hi', hp, hn, ho, nu32, intBinOp, parseInv, counterVariant, Expr.u32, Val.u32, Val.ofInt]
    have h1 : (i + 1) % 4294967296 = i + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨⟨i + 1, by omega, by rw [BitVec.ofNat_add_ofNat], ?_, ?_, fun j c hj hjc => ?_⟩, by omega⟩
    · rw [hstep]
    · rw [hstep]; exact hnew
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hdig j c hj hjc
      · rw [List.getElem?_eq_getElem hc] at hjc; cases hjc; exact ⟨hd1, hd2⟩

end Examples.ParseU32

#print axioms Examples.ParseU32.parseU32_correct
