import LC

/-!
# CRC-32, bit by bit

```c
uint32_t crc32(const uint8_t *p, uint32_t n);
```

The standard CRC-32 (CRC-32/ISO-HDLC: zlib, PNG, Ethernet) of the `n` bytes at `p`: reflected
input and output, polynomial `0xEDB88320` (the reflected `0x04C11DB7`), initial value and final
XOR `0xFFFFFFFF`. No lookup table: eight shift-and-conditional-XOR steps per byte, done
branch-free with the mask `0 - (c & 1)`.

The reference is the textbook bitwise CRC over `BitVec 32`. It is tested against an independent
oracle, polynomial long division over GF(2) on bit-reversed bytes, and against the published
check value. The proof shows the C function returns exactly the reference's value for every
buffer of length < 2³², and leaves memory unchanged. The nested loop (bytes, then bits) is two
`lc_while`s; the problem-specific lemmas are the branch-free step (by `bv_decide`) and how the
reference extends by one byte.
-/

open LC LC.Check

namespace Examples.Crc32

/-! ## 1. The reference -/

/-- The reflected CRC-32 polynomial. -/
def poly : BitVec 32 := 0xEDB88320

/-- One bit of the reflected CRC: shift right, and XOR in the polynomial if a 1 fell out. -/
def stepBit (c : BitVec 32) : BitVec 32 :=
  if c &&& 1 = 1 then (c >>> 1) ^^^ poly else c >>> 1

/-- `k` bit steps. -/
def bits : Nat → BitVec 32 → BitVec 32
  | 0, c => c
  | k + 1, c => stepBit (bits k c)

/-- One byte: XOR it into the low bits, then eight bit steps. -/
def stepByte (c : BitVec 32) (b : BitVec 8) : BitVec 32 := bits 8 (c ^^^ BitVec.ofNat 32 b.toNat)

/-- The register after the bytes `xs`, starting from `0xFFFFFFFF`. -/
def crcReg (xs : List (BitVec 8)) : BitVec 32 := xs.foldl stepByte 0xFFFFFFFF

/-- CRC-32 of a byte string. -/
def crc32Ref (xs : List (BitVec 8)) : BitVec 32 := crcReg xs ^^^ 0xFFFFFFFF

/-! ## 2. Test the reference -/

def bytesOf (s : String) : List (BitVec 8) := s.toUTF8.toList.map (fun b => BitVec.ofNat 8 b.toNat)

#guard crc32Ref [] = 0
#guard crc32Ref (bytesOf "123456789") = 0xCBF43926              -- the published check value
#guard crc32Ref (bytesOf "a") = 0xE8B7BE43
#guard crc32Ref (bytesOf "The quick brown fox jumps over the lazy dog") = 0x414FA339
#guard crc32Ref [0] = 0xD202EF8D
#guard crc32Ref [0xFF, 0xFF, 0xFF, 0xFF] = 0xFFFFFFFF

/-! An independent oracle: CRC as polynomial division over GF(2), most significant bit first.
Bytes are bit-reversed (the "reflected input"), the message is `M(x)·x³² + 0xFFFFFFFF·x^(8n)`
(the initial value), the remainder modulo `0x104C11DB7` is bit-reversed back and XORed with
`0xFFFFFFFF`. Polynomials are `Nat`s. -/

def revBits (w a : Nat) : Nat := (List.range w).foldl (fun r k => if a.testBit k then r ||| (1 <<< (w - 1 - k)) else r) 0

def polyMod (a nbits : Nat) : Nat :=
  (List.range nbits).reverse.foldl
    (fun a k => if 32 ≤ k && a.testBit k then a ^^^ (0x104C11DB7 <<< (k - 32)) else a) a

def crcDiv (xs : List (BitVec 8)) : Nat :=
  let m := xs.foldl (fun m b => m * 256 + revBits 8 b.toNat) 0
  let a := (m <<< 32) ^^^ (0xFFFFFFFF <<< (8 * xs.length))
  revBits 32 (polyMod a (8 * xs.length + 32)) ^^^ 0xFFFFFFFF

#guard crcDiv (bytesOf "123456789") = 0xCBF43926

def genBytes : Gen (List (BitVec 8)) := Gen.list 12 (Gen.bv 8)

#guard forAll genBytes fun xs => (crc32Ref xs).toNat == crcDiv xs
-- CRC is affine: for equal lengths, crc(x ⊕ y ⊕ z) = crc x ⊕ crc y ⊕ crc z.
#guard forAll (do let n ← Gen.below 10; return (← Gen.vector n (Gen.bv 8), ← Gen.vector n (Gen.bv 8),
    ← Gen.vector n (Gen.bv 8))) fun (x, y, z) =>
  crc32Ref (List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) x y) z) ==
    crc32Ref x ^^^ crc32Ref y ^^^ crc32Ref z

/-! ## 3. The code

```c
uint32_t crc32(const uint8_t *p, uint32_t n) {
  uint32_t c = 0xFFFFFFFFu;
  uint32_t i = 0u;
  while (i < n) {
    uint8_t b = p[i];
    c = c ^ (uint32_t)b;
    uint32_t j = 0u;
    while (j < 8u) {
      c = (c >> 1u) ^ (0xEDB88320u & (0u - (c & 1u)));
      j = j + 1u;
    }
    i = i + 1u;
  }
  return c ^ 0xFFFFFFFFu;
}
```
-/

def crc32 : Fn where
  name   := "crc32"
  params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("j", .int .u32), ("b", .int .u8), ("c", .int .u32)]
  body   := .block [
    "c" ::= .u32 0xFFFFFFFF,
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "b" (v "p") (v "i"),
      "c" ::= v "c" ^^^ .cast .u32 (v "b"),
      "j" ::= .u32 0,
      .while (v "j" <. .u32 8) (.block [
        "c" ::= (v "c" >>> Expr.u32 1) ^^^ (Expr.u32 0xEDB88320 &&& (Expr.u32 0 - (v "c" &&& Expr.u32 1))),
        "j" ::= v "j" + .u32 1
      ]),
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u32
  result := v "c" ^^^ .u32 0xFFFFFFFF

#guard crc32.typeCheck
#guard (cTranslationUnit [crc32]).isOk

/-! ## 4. Test the code against the reference -/

def runCrc32 (xs : List (BitVec 8)) : Option (BitVec 32) :=
  let cells := u8s xs
  match crc32.callMem [.ptr .u8 ⟨0, 0⟩, .u32 xs.length]
      [(0, if cells.isEmpty then [.u8 0] else cells)] with
  | .ok (.int .u32 r, _) => some r
  | _ => none

#guard runCrc32 (bytesOf "123456789") == some 0xCBF43926
#guard runCrc32 [] == some 0
#guard forAll genBytes fun xs => runCrc32 xs == some (crc32Ref xs)

/-! ## 5. The proof: `crc32` refines `crc32Ref` -/

/-- The branch-free bit step in the code is the reference's `stepBit`. -/
theorem stepBit_eq (c : BitVec 32) :
    (c >>> 1 ^^^ 3988292384#32 &&& -(c &&& 1#32)) = stepBit c := by
  have hbit : c &&& 1#32 = 0#32 ∨ c &&& 1#32 = 1#32 := by
    have h1 : (c &&& 1#32).toNat = c.toNat % 2 := by simp [BitVec.toNat_and, Nat.and_one_is_mod]
    rcases Nat.mod_two_eq_zero_or_one c.toNat with h | h
    · exact .inl (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
    · exact .inr (BitVec.eq_of_toNat_eq (by rw [h1, h]; rfl))
  rcases hbit with h | h <;> simp [h, stepBit, poly]

/-- One more step of the inner loop, in the shape `lc_auto` leaves it. -/
theorem bits_step (k : Nat) (c : BitVec 32) :
    (bits k c >>> 1 ^^^ 3988292384#32 &&& -(bits k c &&& 1#32)) = bits (k + 1) c :=
  stepBit_eq (bits k c)

/-- How the register extends by one byte. -/
theorem crcReg_take_succ {xs : List (BitVec 8)} {i : Nat} {b : BitVec 8} (hb : xs[i]? = some b) :
    crcReg (xs.take (i + 1)) = stepByte (crcReg (xs.take i)) b := by
  have hi : i < xs.length := by
    rcases Nat.lt_or_ge i xs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  rw [List.getElem?_eq_getElem hi] at hb; cases hb
  simp only [crcReg, List.take_succ_eq_append_getElem hi, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The inner loop's variant: `8 - j`. -/
def jVar : Store → Heap → Nat := fun st _ =>
  match st.get "j" with
  | some (.int _ bv) => 8 - bv.toNat
  | _ => 0

def outerInv (p : Ptr) (xs : List (BitVec 8)) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ xs.length ∧ st.get "p" = some (.ptr .u8 p) ∧ st.get "n" = some (nu32 xs.length) ∧
    st.get "i" = some (nu32 i) ∧ st.get "c" = some (.int .u32 (crcReg (xs.take i))) ∧ h = h₀

/-- The inner loop, for byte `i`: `k` bit steps done. -/
def innerInv (p : Ptr) (xs : List (BitVec 8)) (h₀ : Heap) (i : Nat) : SProp := fun st h =>
  ∃ k b, i < xs.length ∧ k ≤ 8 ∧ xs[i]? = some b ∧ st.get "p" = some (.ptr .u8 p) ∧
    st.get "n" = some (nu32 xs.length) ∧ st.get "i" = some (nu32 i) ∧
    st.get "j" = some (nu32 k) ∧
    st.get "c" = some (.int .u32 (bits k (crcReg (xs.take i) ^^^ BitVec.ofNat 32 b.toNat))) ∧ h = h₀

/-- **`crc32` returns exactly `crc32Ref xs`**, for any byte buffer of length < 2³², inside any
memory, and leaves memory unchanged. -/
theorem crc32_refines (P : Program) (p : Ptr) (xs : List (BitVec 8))
    (hlen : xs.length < 2 ^ 32) (h hf : Heap) (m : Mem) (ha : array p (u8s xs) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ m', crc32.Returns P [.ptr .u8 p, .u32 xs.length] m (.int .u32 (crc32Ref xs)) m' ∧
      m'.heap = m.heap := by
  have hinit : crc32.initStore [.ptr .u8 p, .u32 xs.length] =
      some [("p", .ptr .u8 p), ("n", nu32 xs.length)] := by
    simp [Fn.initStore, crc32, Store.empty]; repeat' constructor
  suffices hbody : swp P crc32.body (fun st h' => ∃ v, crc32.result.eval st = some v ∧
      v.ty = crc32.ret ∧ (v = .int .u32 (crc32Ref xs) ∧ h' = h)) _ h by
    obtain ⟨v, m', h', hret, -, hm', rfl, rfl⟩ := Fn.returns_of_swp
      (post := fun v h' => v = .int .u32 (crc32Ref xs) ∧ h' = h) hinit hbody d hm
    exact ⟨m', hret, by rw [hm', hm]⟩
  lc_auto
  lc_while (outerInv p xs h) (counterVariant xs.length) [outerInv, counterVariant]
  lc_while (innerInv p xs ‹Heap› ‹Nat›) jVar [innerInv, jVar, bits_step, outerInv, counterVariant,
    crcReg_take_succ, stepByte]
  · -- the witness for the byte is `xs[i]`, and the invariant's `b` is that byte
    obtain ⟨_, hb⟩ := List.getElem?_eq_some_iff.mp ‹xs[_]? = some _›
    rw [hb]

#print axioms crc32_refines

end Examples.Crc32
