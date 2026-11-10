import LC.Interp

/-!
# Property testing inside Lean, for the spec-first workflow

The spec is the one thing a proof can't check. So before proving anything, test it:

1. Write the reference as a plain Lean function (`decVal`, `xs.count x`, a `List` queue).
2. `#guard Check.forAll gen prop`: test the reference against properties, or against an
   independent oracle (`String.toNat?`, `List.mergeSort`).
3. `#guard Check.forAll gen fun a => observe (run f a) == ref a`: test the LC code against the
   reference on random inputs, in the interpreter.
4. Only then prove the refinement theorem.

Everything here is pure and deterministic (a fixed seed), so the checks run at elaboration
time in `#guard`, and fail the build when they fail. Use `Check.counterexample?` with `#eval`
to see a failing input.
-/

namespace LC.Check

/-- A splitmix64 generator. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9e3779b97f4a7c15
  let z := (s ^^^ (s >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.ofSeed (seed : Nat) : Rng := ⟨UInt64.ofNat (seed * 2654435761 + 1)⟩

/-- A random generator of `α`s. -/
def Gen (α : Type) := Rng → α × Rng

instance : Monad Gen where
  pure a := fun r => (a, r)
  bind g f := fun r => let (a, r) := g r; f a r

namespace Gen

/-- A natural number in `[0, n)` (`0` when `n = 0`). -/
def below (n : Nat) : Gen Nat := fun r =>
  let (x, r) := r.next
  (if n = 0 then 0 else x.toNat % n, r)

/-- A natural number in `[lo, hi]`. -/
def range (lo hi : Nat) : Gen Nat := do return lo + (← below (hi + 1 - lo))

def bool : Gen Bool := do return (← below 2) == 1

/-- A uniformly random `BitVec w`. -/
def bv (w : Nat) : Gen (BitVec w) := fun r =>
  let (a, r) := r.next
  let (b, r) := r.next
  (BitVec.ofNat w (a.toNat * 2 ^ 64 + b.toNat), r)

/-- One of the given values. -/
def elements {α} [Inhabited α] (xs : List α) : Gen α := do return xs[← below xs.length]!

/-- Pick a generator with the given weights. -/
def frequency {α} [Inhabited α] (gs : List (Nat × Gen α)) : Gen α := do
  let total := (gs.map (·.1)).foldl (· + ·) 0
  let mut k ← below total
  for (w, g) in gs do
    if k < w then return ← g
    k := k - w
  return default

/-- A list of exactly `n` elements. -/
def vector {α} (n : Nat) (g : Gen α) : Gen (List α) := fun r =>
  (List.range n).foldl (fun (acc, r) _ => let (a, r) := g r; (acc ++ [a], r)) ([], r)

/-- A list of length `0..maxLen`. -/
def list {α} (maxLen : Nat) (g : Gen α) : Gen (List α) := do vector (← below (maxLen + 1)) g

/-- A `BitVec w` that is usually small (so equalities and orderings between random values
actually happen), sometimes an edge value, sometimes anything. -/
def bvSmall (w : Nat) : Gen (BitVec w) :=
  frequency [(6, do return BitVec.ofNat w (← below 8)),
             (1, elements [0, BitVec.allOnes w, BitVec.ofNat w (2 ^ (w - 1))]),
             (2, bv w)]

/-- A list sorted as unsigned numbers. -/
def sortedList (maxLen : Nat) (g : Gen (BitVec w)) : Gen (List (BitVec w)) := do
  return (← list maxLen g).mergeSort (·.toNat ≤ ·.toNat)

end Gen

/-- `n` generated inputs, from `seed`. -/
def samples {α} (g : Gen α) (n : Nat := 200) (seed : Nat := 0) : List α :=
  ((List.range n).foldl (fun (acc, r) _ => let (a, r) := g r; (a :: acc, r))
    ([], Rng.ofSeed seed)).1.reverse

/-- Does `p` hold on `n` random inputs? For `#guard`. -/
def forAll {α} (g : Gen α) (p : α → Bool) (n : Nat := 200) (seed : Nat := 0) : Bool :=
  (samples g n seed).all p

/-- The first random input on which `p` fails, if any. For `#eval`. -/
def counterexample? {α} (g : Gen α) (p : α → Bool) (n : Nat := 200) (seed : Nat := 0) :
    Option α :=
  (samples g n seed).find? (! p ·)

end LC.Check
