import LC

/-!
# `base64_encode`: RFC 4648 base64, proved to write exactly the reference encoding

```c
uint8_t  b64_sym(uint8_t x);                                          // alphabet[x & 63]
uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out);  // returns 4*ceil(n/3)
```

`base64_encode` encodes the `n` bytes at `in` into `out` (alphabet `A–Z a–z 0–9 + /`, `=`
padding, no line breaks) and returns the number of bytes written. The theorem says: for any
`n ≤ 3221225469` and separate buffers, `out` ends up holding exactly `encRef in` (the
reference encoding), which has length `4 * ceil(n / 3)`, that number is returned, `in` is
unchanged, and nothing else in memory is touched.

The reference works on whole 3-byte groups; it is checked against the RFC test vectors and
against an independent bit-stream encoder (bytes → bits → 6-bit chunks → symbols → padding).
-/

open LC LC.Check

namespace Examples.Base64

/-! ## 1. The reference -/

/-- The RFC 4648 §4 alphabet. -/
def alphabet : List Char := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList

/-- The symbol for a 6-bit value (the low 6 bits of `x`), as an ASCII byte. -/
def sym (x : BitVec 8) : BitVec 8 := BitVec.ofNat 8 (alphabet.getD (x.toNat % 64) 'A').toNat

/-- `'='`. -/
def pad : BitVec 8 := 61

/-- Base64 of a byte string: each 3-byte group becomes 4 symbols; a final 1- or 2-byte group
becomes 2 or 3 symbols plus `=` padding. -/
def encRef : List (BitVec 8) → List (BitVec 8)
  | a :: b :: c :: rest =>
    [sym (a >>> 2), sym (((a &&& 3) <<< 4) ||| (b >>> 4)), sym (((b &&& 15) <<< 2) ||| (c >>> 6)),
      sym c] ++ encRef rest
  | [a, b] => [sym (a >>> 2), sym (((a &&& 3) <<< 4) ||| (b >>> 4)), sym ((b &&& 15) <<< 2), pad]
  | [a] => [sym (a >>> 2), sym ((a &&& 3) <<< 4), pad, pad]
  | [] => []

/-! ## 2. Test the reference -/

def bytesOf (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat
def strOf (xs : List (BitVec 8)) : String := String.ofList (xs.map fun b => Char.ofNat b.toNat)

-- RFC 4648 §10 test vectors.
#guard strOf (encRef (bytesOf "")) == ""
#guard strOf (encRef (bytesOf "f")) == "Zg=="
#guard strOf (encRef (bytesOf "fo")) == "Zm8="
#guard strOf (encRef (bytesOf "foo")) == "Zm9v"
#guard strOf (encRef (bytesOf "foob")) == "Zm9vYg=="
#guard strOf (encRef (bytesOf "fooba")) == "Zm9vYmE="
#guard strOf (encRef (bytesOf "foobar")) == "Zm9vYmFy"
-- High bytes reach the last symbols of the alphabet.
#guard strOf (encRef [0xff, 0xff, 0xff]) == "////"
#guard strOf (encRef [0xfb, 0xef, 0xbe]) == "++++"
#guard strOf (encRef [0, 0, 0]) == "AAAA"

/-- An independent encoder: the input as a bit stream (MSB first), cut into 6-bit chunks
(the last one zero-filled), each mapped through the alphabet, then `=` up to a multiple of 4. -/
def bitsOf (xs : List (BitVec 8)) : List Bool :=
  xs.flatMap fun b => (List.range 8).reverse.map fun k => b.toNat.testBit k

def chunks6 : Nat → List Bool → List Nat
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, bs =>
    let c := (bs.take 6 ++ List.replicate (6 - (bs.take 6).length) false).foldl
      (fun acc b => 2 * acc + if b then 1 else 0) 0
    c :: chunks6 f (bs.drop 6)

def oracle (xs : List (BitVec 8)) : String :=
  let bs := bitsOf xs
  let cs := (chunks6 bs.length bs).map fun k => alphabet.getD k '?'
  String.ofList (cs ++ List.replicate ((4 - cs.length % 4) % 4) '=')

def genBytes : Gen (List (BitVec 8)) := Gen.list 13 (Gen.bv 8)

#guard forAll genBytes fun xs => strOf (encRef xs) == oracle xs
#guard forAll genBytes fun xs => (encRef xs).length == 4 * ((xs.length + 2) / 3)
-- The generator hits every length class.
#guard [0, 1, 2].all fun r => (samples genBytes).any fun xs => xs.length % 3 == r && xs.length > 3

/-! ## 3. The code

```c
uint8_t b64_sym(uint8_t x) {
  uint8_t y = x & 63;
  if (y < 26) return y + 65;     // 'A'..'Z'
  if (y < 52) return y + 71;     // 'a'..'z'
  if (y < 62) return y - 4;      // '0'..'9'
  if (y == 62) return 43;        // '+'
  return 47;                     // '/'
}

uint32_t base64_encode(const uint8_t *in, uint32_t n, uint8_t *out) {
  uint32_t i = 0, j = 0;
  while (3 <= n - i) {
    a = in[i]; b = in[i + 1]; c = in[i + 2];
    out[j]     = b64_sym(a >> 2);
    out[j + 1] = b64_sym(((a & 3) << 4) | (b >> 4));
    out[j + 2] = b64_sym(((b & 15) << 2) | (c >> 6));
    out[j + 3] = b64_sym(c);
    i = i + 3; j = j + 4;
  }
  if (n - i == 1) { ... two symbols, "==" ... }
  else if (n - i == 2) { ... three symbols, "=" ... }
  return j;
}
```
-/

def b64Sym : Fn where
  name   := "b64_sym"
  params := [("x", .int .u8)]
  locals := [("y", .int .u8)]
  body   := .block [
    "y" ::= v "x" &&& Expr.u8 63,
    .ite (v "y" <. .u8 26) (.ret (v "y" + .u8 65)) .skip,
    .ite (v "y" <. .u8 52) (.ret (v "y" + .u8 71)) .skip,
    .ite (v "y" <. .u8 62) (.ret (v "y" - .u8 4)) .skip,
    .ite (v "y" ==. .u8 62) (.ret (.u8 43)) .skip
  ]
  ret    := .int .u8
  result := .u8 47

def base64Encode : Fn where
  name   := "base64_encode"
  params := [("in", .ptr .u8), ("n", .int .u32), ("out", .ptr .u8)]
  locals := [("i", .int .u32), ("j", .int .u32), ("a", .int .u8), ("b", .int .u8),
             ("c", .int .u8), ("s", .int .u8)]
  body   := .block [
    "i" ::= .u32 0,
    "j" ::= .u32 0,
    .while (.u32 3 <=. v "n" - v "i") (.block [
      .load "a" (v "in") (v "i"),
      .load "b" (v "in") (v "i" + .u32 1),
      .load "c" (v "in") (v "i" + .u32 2),
      .call (some "s") "b64_sym" [v "a" >>> Expr.u8 2],
      .store (v "out") (v "j") (v "s"),
      .call (some "s") "b64_sym" [((v "a" &&& Expr.u8 3) <<< Expr.u8 4) ||| (v "b" >>> Expr.u8 4)],
      .store (v "out") (v "j" + .u32 1) (v "s"),
      .call (some "s") "b64_sym" [((v "b" &&& Expr.u8 15) <<< Expr.u8 2) ||| (v "c" >>> Expr.u8 6)],
      .store (v "out") (v "j" + .u32 2) (v "s"),
      .call (some "s") "b64_sym" [v "c"],
      .store (v "out") (v "j" + .u32 3) (v "s"),
      "i" ::= v "i" + .u32 3,
      "j" ::= v "j" + .u32 4
    ]),
    .ite (v "n" - v "i" ==. .u32 1) (.block [
      .load "a" (v "in") (v "i"),
      .call (some "s") "b64_sym" [v "a" >>> Expr.u8 2],
      .store (v "out") (v "j") (v "s"),
      .call (some "s") "b64_sym" [(v "a" &&& Expr.u8 3) <<< Expr.u8 4],
      .store (v "out") (v "j" + .u32 1) (v "s"),
      .store (v "out") (v "j" + .u32 2) (.u8 61),
      .store (v "out") (v "j" + .u32 3) (.u8 61),
      "j" ::= v "j" + .u32 4
    ]) (.ite (v "n" - v "i" ==. .u32 2) (.block [
      .load "a" (v "in") (v "i"),
      .load "b" (v "in") (v "i" + .u32 1),
      .call (some "s") "b64_sym" [v "a" >>> Expr.u8 2],
      .store (v "out") (v "j") (v "s"),
      .call (some "s") "b64_sym" [((v "a" &&& Expr.u8 3) <<< Expr.u8 4) ||| (v "b" >>> Expr.u8 4)],
      .store (v "out") (v "j" + .u32 1) (v "s"),
      .call (some "s") "b64_sym" [(v "b" &&& Expr.u8 15) <<< Expr.u8 2],
      .store (v "out") (v "j" + .u32 2) (v "s"),
      .store (v "out") (v "j" + .u32 3) (.u8 61),
      "j" ::= v "j" + .u32 4
    ]) .skip)
  ]
  ret    := .int .u32
  result := v "j"

def prog : Program := [b64Sym, base64Encode]

#guard b64Sym.typeCheck prog && base64Encode.typeCheck prog
#guard (cTranslationUnit prog).isOk

/-! ## 4. Test the code against the reference -/

/-- Run `base64_encode` on `xs` (block 0) with an output buffer of exactly the right size
(block 1); the returned count and the output buffer. -/
def runEnc (xs : List (BitVec 8)) : Option (Nat × List Val) :=
  let inc := u8s xs
  let outc := List.replicate (4 * ((xs.length + 2) / 3)) (Val.u8 0)
  match base64Encode.callMem [.ptr .u8 ⟨0, 0⟩, .u32 xs.length, .ptr .u8 ⟨1, 0⟩]
      [(0, if inc.isEmpty then [.u8 0] else inc), (1, if outc.isEmpty then [.u8 0] else outc)]
      (P := prog) with
  | .ok (.int .u32 r, m) => (m.cells 1).map fun cs => (r.toNat, cs)
  | _ => none

#guard forAll genBytes fun xs =>
  runEnc xs == some ((encRef xs).length, if xs.isEmpty then [.u8 0] else u8s (encRef xs))
#guard (List.range 64).all fun k =>
  b64Sym.call [.u8 k] (P := prog) == .ok (.int .u8 (sym (BitVec.ofNat 8 k)))

/-! ## 5. The proofs

### `b64_sym` -/

/-- The if-chain `b64_sym` computes, as a Lean function. -/
def symArith (x : BitVec 8) : BitVec 8 :=
  let y := x &&& 63
  if y.toNat < 26 then y + 65 else if y.toNat < 52 then y + 71 else if y.toNat < 62 then y - 4
  else if y = 62 then 43 else 47

/-- The alphabet as a list of characters (so the kernel need not unfold `String.toList`). -/
theorem alphabet_eq : alphabet = ['A','B','C','D','E','F','G','H','I','J','K','L','M','N','O',
    'P','Q','R','S','T','U','V','W','X','Y','Z','a','b','c','d','e','f','g','h','i','j','k','l',
    'm','n','o','p','q','r','s','t','u','v','w','x','y','z','0','1','2','3','4','5','6','7','8',
    '9','+','/'] := by
  simp [alphabet]

/-- The arithmetic agrees with the alphabet table, on all 256 inputs. -/
theorem symArith_eq : ∀ x : BitVec 8, symArith x = sym x := by
  simp only [sym, alphabet_eq]; decide

theorem b64Sym_spec (P : Program) (x : BitVec 8) :
    swpo P b64Sym.body (fun o st h' => ∃ v, b64Sym.finish o st = some v ∧
      v = .int .u8 (sym x) ∧ h' = Heap.empty) [("x", .int .u8 x)] Heap.empty := by
  rw [← symArith_eq]
  lc_auto [symArith]

theorem b64Sym_init (x : BitVec 8) : b64Sym.initStore [.int .u8 x] = some [("x", .int .u8 x)] := by
  simp [Fn.initStore, b64Sym, Store.empty]; rfl

/-! ### Facts about `encRef` -/

/-- The output length is `4 * ceil(n / 3)`. -/
theorem encRef_length : ∀ xs : List (BitVec 8), (encRef xs).length = 4 * ((xs.length + 2) / 3)
  | _ :: _ :: _ :: rest => by simp [encRef, encRef_length rest]; omega
  | [_, _] => by simp [encRef]
  | [_] => by simp [encRef]
  | [] => by simp [encRef]


/-- Whole groups encode independently. -/
theorem encRef_append : ∀ (l₁ l₂ : List (BitVec 8)), l₁.length % 3 = 0 →
    encRef (l₁ ++ l₂) = encRef l₁ ++ encRef l₂
  | a :: b :: c :: rest, l₂, h => by
    simp only [List.cons_append, encRef, List.append_assoc]
    rw [encRef_append rest l₂ (by simp at h; omega)]
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | [_, _], _, h => by simp at h

theorem take_add_three {xs : List (BitVec 8)} {w : Nat} (hi : w + 3 ≤ xs.length) :
    xs.take (w + 3) = xs.take w ++ [xs[w], xs[w + 1], xs[w + 2]] := by
  rw [List.take_add, List.drop_eq_getElem_cons (by omega : w < xs.length),
    List.drop_eq_getElem_cons (by omega : w + 1 < xs.length),
    List.drop_eq_getElem_cons (by omega : w + 1 + 1 < xs.length)]
  rfl

/-- Four writes at the front of a list of length ≥ 4. -/
theorem set_four {α} (D : List α) (a b c d : α) (k₁ k₂ k₃ : Nat) (h₁ : k₁ = 1) (h₂ : k₂ = 2)
    (h₃ : k₃ = 3) (hD : 4 ≤ D.length) :
    (((D.set 0 a).set k₁ b).set k₂ c).set k₃ d = [a, b, c, d] ++ D.drop 4 := by
  subst h₁ h₂ h₃
  match D, hD with
  | _ :: _ :: _ :: _ :: _, _ => rfl

/-- The loop step: one more whole group written. -/
theorem step_group (xs ds : List (BitVec 8)) (w k₁ k₂ k₃ : Nat) (hw : w % 3 = 0)
    (hi : w + 3 ≤ xs.length) (hd : ds.length = 4 * ((xs.length + 2) / 3))
    (h₁ : k₁ = 1) (h₂ : k₂ = 2) (h₃ : k₃ = 3) :
    u8s (encRef (xs.take w)) ++
      (((((u8s ds).drop (4 * (w / 3))).set 0 (.int .u8 (sym (xs[w] >>> 2)))).set k₁
        (.int .u8 (sym ((xs[w] &&& 3#8) <<< 4 ||| xs[w + 1] >>> 4)))).set k₂
        (.int .u8 (sym ((xs[w + 1] &&& 15#8) <<< 2 ||| xs[w + 2] >>> 6)))).set k₃
        (.int .u8 (sym xs[w + 2])) =
    u8s (encRef (xs.take (w + 3))) ++ (u8s ds).drop (4 * (w / 3 + 1)) := by
  rw [set_four _ _ _ _ _ _ _ _ h₁ h₂ h₃ (by simp; omega), take_add_three hi,
    encRef_append _ _ (by simp; omega)]
  simp [encRef, List.drop_drop, Nat.mul_add, Nat.add_comm]

/-- The tail with one byte left. -/
theorem tail_one (xs ds : List (BitVec 8)) (w k₁ k₂ k₃ : Nat) (hw : w % 3 = 0)
    (hi : xs.length = w + 1) (hd : ds.length = 4 * ((xs.length + 2) / 3))
    (h₁ : k₁ = 1) (h₂ : k₂ = 2) (h₃ : k₃ = 3) :
    u8s (encRef (xs.take w)) ++
      (((((u8s ds).drop (4 * (w / 3))).set 0 (.int .u8 (sym (xs[w] >>> 2)))).set k₁
        (.int .u8 (sym ((xs[w] &&& 3#8) <<< 4)))).set k₂ (.int .u8 61#8)).set k₃ (.int .u8 61#8) =
    u8s (encRef xs) := by
  rw [set_four _ _ _ _ _ _ _ _ h₁ h₂ h₃ (by simp; omega)]
  conv => rhs; rw [← List.take_length (l := xs), hi, List.take_succ_eq_append_getElem (by omega),
    encRef_append _ _ (by simp; omega)]
  simp [encRef, pad, List.drop_eq_nil_of_le (by simp; omega : (u8s ds).length ≤ 4 * (w / 3) + 4)]

/-- The tail with two bytes left. -/
theorem tail_two (xs ds : List (BitVec 8)) (w k₁ k₂ k₃ : Nat) (hw : w % 3 = 0)
    (hi : xs.length = w + 2) (hd : ds.length = 4 * ((xs.length + 2) / 3))
    (h₁ : k₁ = 1) (h₂ : k₂ = 2) (h₃ : k₃ = 3) :
    u8s (encRef (xs.take w)) ++
      (((((u8s ds).drop (4 * (w / 3))).set 0 (.int .u8 (sym (xs[w] >>> 2)))).set k₁
        (.int .u8 (sym ((xs[w] &&& 3#8) <<< 4 ||| xs[w + 1] >>> 4)))).set k₂
        (.int .u8 (sym ((xs[w + 1] &&& 15#8) <<< 2)))).set k₃ (.int .u8 61#8) =
    u8s (encRef xs) := by
  rw [set_four _ _ _ _ _ _ _ _ h₁ h₂ h₃ (by simp; omega)]
  conv => rhs; rw [← List.take_length (l := xs), hi, List.take_succ_eq_append_getElem (by omega),
    List.take_succ_eq_append_getElem (by omega), List.append_assoc,
    encRef_append _ _ (by simp; omega)]
  simp [encRef, pad, List.drop_eq_nil_of_le (by simp; omega : (u8s ds).length ≤ 4 * (w / 3) + 4)]

/-- Exit with nothing left. -/
theorem tail_zero (xs ds : List (BitVec 8)) (w : Nat) (hw : w % 3 = 0) (hi : xs.length = w)
    (hd : ds.length = 4 * ((xs.length + 2) / 3)) :
    u8s (encRef (xs.take w)) ++ (u8s ds).drop (4 * (w / 3)) = u8s (encRef xs) := by
  subst hi
  simp [List.drop_eq_nil_of_le (by simp; omega : (u8s ds).length ≤ 4 * (xs.length / 3))]

/-! ### `base64_encode` -/

/-- Invariant: `i` is a multiple of 3, the first `4 * (i / 3)` bytes of `out` hold the encoding
of the first `i` input bytes, and the rest of `out` is untouched. -/
def encInv (pin pout : Ptr) (xs ds : List (BitVec 8)) : SProp := fun st h =>
  ∃ i, i % 3 = 0 ∧ i ≤ xs.length ∧ st.get "in" = some (.ptr .u8 pin) ∧
    st.get "n" = some (nu32 xs.length) ∧ st.get "out" = some (.ptr .u8 pout) ∧
    st.get "i" = some (nu32 i) ∧ st.get "j" = some (nu32 (4 * (i / 3))) ∧
    (array pout (u8s (encRef (xs.take i) ++ ds.drop (4 * (i / 3)))) ∗ array pin (u8s xs)) h

/-- **`base64_encode` writes exactly `encRef xs`.** For input bytes `xs` with
`xs.length ≤ 3221225469` and a separate output buffer of `4 * ceil(n / 3)` bytes, it returns
`4 * ceil(n / 3)`, the output buffer holds `encRef xs` afterwards, the input is unchanged, and the
rest of memory is untouched. Holds in any program where `b64_sym` is the verified one. -/
theorem base64Encode_refines (P : Program) (hP : P.find? "b64_sym" = some b64Sym)
    (pin pout : Ptr) (xs ds : List (BitVec 8)) (hlen : xs.length ≤ 3221225469)
    (hd : ds.length = 4 * ((xs.length + 2) / 3)) (h hf : Heap) (m : Mem)
    (hpre : (array pout (u8s ds) ∗ array pin (u8s xs)) h) (d : h.Disjoint hf)
    (hm : m.heap = h.union hf) :
    ∃ m' h', base64Encode.Returns P [.ptr .u8 pin, .u32 xs.length, .ptr .u8 pout] m
        (nu32 (4 * ((xs.length + 2) / 3))) m' ∧
      h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      (array pout (u8s (encRef xs)) ∗ array pin (u8s xs)) h' := by
  have hinit : base64Encode.initStore [.ptr .u8 pin, .u32 xs.length, .ptr .u8 pout] =
      some [("in", .ptr .u8 pin), ("n", nu32 xs.length), ("out", .ptr .u8 pout)] := by
    simp [Fn.initStore, base64Encode, Store.empty]; repeat' constructor
  let post : Val → HProp := fun v h' => v = nu32 (4 * ((xs.length + 2) / 3)) ∧
    (array pout (u8s (encRef xs)) ∗ array pin (u8s xs)) h'
  suffices hbody : swpo P base64Encode.body
      (fun o st h' => ∃ v, base64Encode.finish o st = some v ∧ post v h') _ h by
    obtain ⟨v, m', h', hret, d', hm', rfl, hpost⟩ := Fn.returns_of_swpo hinit hbody d hm
    exact ⟨m', h', hret, d', hm', hpost⟩
  lc_auto
  lc_while (encInv pin pout xs ds) (counterVariant xs.length) [encInv, counterVariant, encRef_length]
  repeat lc_call hP (b64Sym_spec P _) (b64Sym_init _) [encInv, counterVariant, encRef_length]
  · exact tail_two xs ds _ _ _ _ ‹_› (by omega) hd (by omega) (by omega) (by omega)
  · exact tail_one xs ds _ _ _ _ ‹_› (by omega) hd (by omega) (by omega) (by omega)
  · exact step_group xs ds _ _ _ _ ‹_› (by omega) hd (by omega) (by omega) (by omega)
  · exact tail_zero xs ds _ ‹_› (by omega) hd

end Examples.Base64

#print axioms Examples.Base64.base64Encode_refines
