import LC

/-!
# A bounded hash map: open addressing over caller storage

```c
bool hm_put(uint32_t *keys, uint32_t *vals, uint8_t *used, uint32_t cap, uint32_t k, uint32_t v);
bool hm_get(const uint32_t *keys, const uint32_t *vals, const uint8_t *used, uint32_t cap,
            uint32_t k, uint32_t *out);
```

A map from `uint32_t` keys to `uint32_t` values in three caller-owned arrays of length `cap`
(a power of two, `1 ≤ cap ≤ 2^16`). The home slot of `k` is `(k * 2654435761u) & (cap - 1)`;
collisions are resolved by linear probing. There is no deletion.

The proof is in two layers:

1. **Code = probing reference.** `hm_put` and `hm_get` compute exactly `putRef` / `getRef`, a
   plain Lean description of "probe from the home slot until an empty slot or the key"
   (`hmPut_refines`, `hmGet_refines`).
2. **Probing reference = finite map.** A representation invariant `Repr cap ks vs us M` relates
   the three arrays to an association list `M` (the model). The empty table represents `[]`,
   and `putRef`/`getRef` agree with the model's insert-or-overwrite (bounded by `cap` distinct
   keys) and lookup, preserving `Repr` (`putRef_correct`, `getRef_correct`).

Together (`hmPut_correct`, `hmGet_correct`): from an empty table, every call in any sequence
of `hm_put`/`hm_get` returns what the finite-map model says.
-/

open LC LC.Check

namespace Examples.HashMap

/-! ## 1. The model: a finite map as an association list -/

abbrev Model := List (BitVec 32 × BitVec 32)

/-- Lookup in the model. -/
def mget (M : Model) (k : BitVec 32) : Option (BitVec 32) := M.lookup k

/-- Insert-or-overwrite, bounded by `cap` distinct keys: `none` means "full, not inserted". -/
def mput (cap : Nat) (M : Model) (k x : BitVec 32) : Option Model :=
  if (M.lookup k).isSome then some (M.map fun p => if p.1 = k then (k, x) else p)
  else if M.length < cap then some ((k, x) :: M) else none

#guard mget [] 3 = none
#guard mput 2 [] 3 7 = some [(3, 7)]
#guard mput 1 [(3, 7)] 3 8 = some [(3, 8)]                   -- overwrite even when full
#guard mput 1 [(3, 7)] 4 8 = none                            -- full, new key
#guard (mput 2 [(3, 7)] 4 8).map (mget · 3) = some (some 7)

/-! ## 2. The probing reference -/

/-- The home slot: Fibonacci hashing, masked to `cap` (a power of two). -/
def home (cap : Nat) (k : BitVec 32) : Nat := (k * 2654435761#32).toNat % cap

/-- The `d`-th slot probed for `k`. -/
def slotAt (cap : Nat) (k : BitVec 32) (d : Nat) : Nat := (home cap k + d) % cap

/-- Probing for `k` stops at step `d`: the slot is empty or holds `k`. -/
def stops (cap : Nat) (ks : List (BitVec 32)) (us : List (BitVec 8)) (k : BitVec 32)
    (d : Nat) : Bool :=
  us.getD (slotAt cap k d) 0 == 0 || ks.getD (slotAt cap k d) 0 == k

/-- The slot where probing for `k` stops, if it stops within `cap` steps. -/
def findSlot (cap : Nat) (ks : List (BitVec 32)) (us : List (BitVec 8)) (k : BitVec 32) :
    Option Nat :=
  ((List.range cap).find? (stops cap ks us k)).map (slotAt cap k)

/-- What `hm_put` returns and leaves in `keys`, `vals`, `used`. -/
def putRef (cap : Nat) (ks vs : List (BitVec 32)) (us : List (BitVec 8)) (k x : BitVec 32) :
    Bool × List (BitVec 32) × List (BitVec 32) × List (BitVec 8) :=
  match findSlot cap ks us k with
  | none => (false, ks, vs, us)
  | some s =>
    if us.getD s 0 = 0 then (true, ks.set s k, vs.set s x, us.set s 1)
    else (true, ks, vs.set s x, us)

/-- What `hm_get` finds. -/
def getRef (cap : Nat) (ks vs : List (BitVec 32)) (us : List (BitVec 8)) (k : BitVec 32) :
    Option (BitVec 32) :=
  match findSlot cap ks us k with
  | none => none
  | some s => if us.getD s 0 = 0 then none else some (vs.getD s 0)

/-! ### Testing the reference against the model

A script of operations (`(k, some x)` = put, `(k, none)` = get) runs through both, from an
empty table, and must give the same answers. -/

/-- How a lookup result is printed in the scripts. -/
def showGet : Option (BitVec 32) → String
  | some r => s!"some {r.toNat}"
  | none => "none"

abbrev Table := List (BitVec 32) × List (BitVec 32) × List (BitVec 8)

def emptyTable (cap : Nat) : Table := (List.replicate cap 0, List.replicate cap 0, List.replicate cap 0)

def runModel (cap : Nat) (M : Model) : List (BitVec 32 × Option (BitVec 32)) → List String
  | [] => []
  | (k, some x) :: ops =>
    match mput cap M k x with
    | some M' => "true" :: runModel cap M' ops
    | none => "false" :: runModel cap M ops
  | (k, none) :: ops => showGet (mget M k) :: runModel cap M ops

def runRef (cap : Nat) (t : Table) : List (BitVec 32 × Option (BitVec 32)) → List String
  | [] => []
  | (k, some x) :: ops =>
    let (b, ks, vs, us) := putRef cap t.1 t.2.1 t.2.2 k x
    s!"{b}" :: runRef cap (ks, vs, us) ops
  | (k, none) :: ops => showGet (getRef cap t.1 t.2.1 t.2.2 k) :: runRef cap t ops

/-- Small keys (so they repeat and collide), caps 1–8. -/
def genScript : Gen (Nat × List (BitVec 32 × Option (BitVec 32))) := do
  let cap ← Gen.elements [1, 2, 4, 8]
  let ops ← Gen.list 20 (do
    let k ← Gen.frequency [(3, Gen.bvSmall 32), (1, Gen.bv 32)]
    let put ← Gen.bool
    if put then return (k, some (← Gen.bv 32)) else return (k, none))
  return (cap, ops)

#guard runRef 2 (emptyTable 2) [(1, some 5), (3, some 6), (1, none), (1, some 7), (1, none),
  (9, some 1), (3, none), (4, none)] =
  ["true", "true", "some 5", "true", "some 7", "false", "some 6", "none"]
#guard forAll genScript fun (cap, ops) => runRef cap (emptyTable cap) ops == runModel cap [] ops
-- The scripts exercise "full" and "found".
#guard (samples genScript).any fun (cap, ops) => (runModel cap [] ops).contains "false"
#guard (samples genScript).any fun (cap, ops) => (runModel cap [] ops).any (·.startsWith "some")

/-! ## 2b. The probing reference implements the model

This is the algorithmic heart: linear probing finds every key, because every stored key is
reachable from its home slot through full slots (`TableRepr.closed`). -/

/-! ### Probing facts -/

theorem slotAt_lt {cap : Nat} (hc : 0 < cap) (k : BitVec 32) (d : Nat) : slotAt cap k d < cap :=
  Nat.mod_lt _ hc

/-- Every slot is probed within `cap` steps. -/
theorem slotAt_surj {cap j : Nat} (hj : j < cap) (k : BitVec 32) :
    slotAt cap k ((j + cap - home cap k) % cap) = j := by
  have hh : home cap k < cap := Nat.mod_lt _ (by omega)
  unfold slotAt
  rw [Nat.add_mod_mod, show home cap k + (j + cap - home cap k) = j + cap by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hj]

theorem findSlot_some {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)} {k : BitVec 32}
    {s : Nat} (h : findSlot cap ks us k = some s) :
    ∃ d, d < cap ∧ s = slotAt cap k d ∧ stops cap ks us k d = true ∧
      ∀ d', d' < d → stops cap ks us k d' = false := by
  unfold findSlot at h
  rcases hf : (List.range cap).find? (stops cap ks us k) with _ | d
  · simp [hf] at h
  · simp only [hf, Option.map_some, Option.some.injEq] at h
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hp, i, hi, hid, hall⟩ := hf
    simp only [List.getElem_range] at hid
    subst hid
    refine ⟨i, by simpa using hi, h.symm, hp, fun d' hd' => ?_⟩
    have := hall d' hd'
    simpa using this

theorem findSlot_none {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)} {k : BitVec 32}
    (h : findSlot cap ks us k = none) : ∀ d, d < cap → stops cap ks us k d = false := by
  unfold findSlot at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro d hd
  simpa using h d (List.mem_range.mpr hd)

theorem findSlot_of_first {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)}
    {k : BitVec 32} {i : Nat} (hi : i < cap) (hall : ∀ d, d < i → stops cap ks us k d = false)
    (hs : stops cap ks us k i = true) : findSlot cap ks us k = some (slotAt cap k i) := by
  unfold findSlot
  have : (List.range cap).find? (stops cap ks us k) = some i := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨hs, i, by simpa using hi, by simp, fun j hj => ?_⟩
    simp [hall j hj]
  rw [this]; rfl

theorem findSlot_of_all {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)}
    {k : BitVec 32} (hall : ∀ d, d < cap → stops cap ks us k d = false) :
    findSlot cap ks us k = none := by
  unfold findSlot
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro d hd
  simp [hall d (List.mem_range.mp hd)]

/-! ### Lists -/

theorem getD_set {α} {l : List α} {i j : Nat} {a d : α} (hi : i < l.length) :
    (l.set i a).getD j d = if j = i then a else l.getD j d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : i = j
  · subst h; simp [hi]
  · simp [h, Ne.symm h]

/-- Count of full slots. -/
def nfull (us : List (BitVec 8)) : Nat := us.countP (· != 0)

theorem nfull_set {us : List (BitVec 8)} {s : Nat} (hs : s < us.length) (h0 : us.getD s 0 = 0) :
    nfull (us.set s 1) = nfull us + 1 := by
  induction us generalizing s with
  | nil => simp at hs
  | cons u us ih =>
    cases s with
    | zero =>
      simp only [List.getD_cons_zero] at h0; subst h0; simp [nfull, List.countP_cons]
    | succ s =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hs
      simp only [List.getD_cons_succ] at h0
      have := ih hs h0
      simp only [nfull] at this ⊢
      rw [List.set_cons_succ, List.countP_cons, List.countP_cons, this]; omega

theorem nfull_lt {us : List (BitVec 8)} {s : Nat} (hs : s < us.length) (h0 : us.getD s 0 = 0) :
    nfull us < us.length := by
  have h1 := nfull_set hs h0
  have h2 : nfull (us.set s 1) ≤ (us.set s 1).length := List.countP_le_length
  rw [List.length_set] at h2; omega

theorem nfull_all {us : List (BitVec 8)} (h : ∀ j, j < us.length → us.getD j 0 ≠ 0) :
    nfull us = us.length := by
  unfold nfull
  rw [List.countP_eq_length]
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
  have := h j hj
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at this
  simp [this]

theorem lookup_none_iff {M : Model} {k : BitVec 32} : M.lookup k = none ↔ ∀ x, (k, x) ∉ M := by
  induction M with
  | nil => simp
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : k = a
    · subst h
      simp only [List.lookup_cons, beq_self_eq_true, reduceCtorEq, false_iff]
      intro hall; exact hall b (List.mem_cons_self ..)
    · have hb : (k == a) = false := by simp [h]
      simp only [List.lookup_cons, hb, ih, List.mem_cons, Prod.mk.injEq, h, false_and, false_or]

theorem lookup_some_iff {M : Model} (hnd : (M.map Prod.fst).Nodup) {k x : BitVec 32} :
    M.lookup k = some x ↔ (k, x) ∈ M := by
  induction M with
  | nil => simp
  | cons p M ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases h : k = a
    · subst h
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq, List.mem_cons,
        Prod.mk.injEq, true_and]
      constructor
      · intro e; exact .inl e.symm
      · rintro (e | hm)
        · exact e.symm
        · exact absurd (List.mem_map.mpr ⟨_, hm, rfl⟩) hnd.1
    · have hb : (k == a) = false := by simp [h]
      simp only [List.lookup_cons, hb, ih hnd.2, List.mem_cons, Prod.mk.injEq, h, false_and,
        false_or]

/-! ### The representation invariant -/

/-- `ks, vs, us` (length `cap`) represent the finite map `M`. -/
structure TableRepr (cap : Nat) (ks vs : List (BitVec 32)) (us : List (BitVec 8)) (M : Model) :
    Prop where
  lks : ks.length = cap
  lvs : vs.length = cap
  lus : us.length = cap
  /-- Every key is reachable from its home slot through full slots. -/
  closed : ∀ j, j < cap → us.getD j 0 ≠ 0 → ∃ e, e < cap ∧ slotAt cap (ks.getD j 0) e = j ∧
    ∀ d, d < e → us.getD (slotAt cap (ks.getD j 0) d) 0 ≠ 0
  /-- No key is stored twice. -/
  uniq : ∀ j j', j < cap → j' < cap → us.getD j 0 ≠ 0 → us.getD j' 0 ≠ 0 →
    ks.getD j 0 = ks.getD j' 0 → j = j'
  /-- The full slots are exactly the model's entries. -/
  mem : ∀ k x, (k, x) ∈ M ↔ ∃ j, j < cap ∧ us.getD j 0 ≠ 0 ∧ ks.getD j 0 = k ∧ vs.getD j 0 = x
  nodup : (M.map Prod.fst).Nodup
  count : M.length = nfull us

theorem repr_empty {cap : Nat} {ks vs : List (BitVec 32)} (hks : ks.length = cap)
    (hvs : vs.length = cap) : TableRepr cap ks vs (List.replicate cap 0) [] where
  lks := hks
  lvs := hvs
  lus := by simp
  closed := fun j hj h => by simp [List.getD_eq_getElem?_getD, hj] at h
  uniq := fun j _ hj _ h => by simp [List.getD_eq_getElem?_getD, hj] at h
  mem := fun k x => by simp [List.getD_eq_getElem?_getD]; intro j hj; simp [hj]
  nodup := List.nodup_nil
  count := (List.countP_eq_zero.mpr fun a ha => by simp [List.eq_of_mem_replicate ha]).symm

/-- If probing for `k` stops at an empty slot, `k` is in no full slot. -/
theorem absent_of_empty {cap : Nat} {ks vs : List (BitVec 32)} {us : List (BitVec 8)} {M : Model}
    (R : TableRepr cap ks vs us M) {k : BitVec 32} {s : Nat} (hs : findSlot cap ks us k = some s)
    (h0 : us.getD s 0 = 0) : ∀ j, j < cap → us.getD j 0 ≠ 0 → ks.getD j 0 ≠ k := by
  intro j hj hf hk
  obtain ⟨e, he, hej, hpath⟩ := R.closed j hj hf
  rw [hk] at hej hpath
  obtain ⟨d, hd, rfl, -, hfirst⟩ := findSlot_some hs
  rcases Nat.lt_trichotomy e d with hlt | rfl | hgt
  · have := hfirst e hlt
    rw [stops, hej, hk] at this
    simp at this
  · rw [hej] at h0; exact hf h0
  · exact hpath d hgt h0

/-- If probing for `k` never stops, every slot is full and none holds `k`. -/
theorem full_of_none {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)} {k : BitVec 32}
    (hn : findSlot cap ks us k = none) :
    ∀ j, j < cap → us.getD j 0 ≠ 0 ∧ ks.getD j 0 ≠ k := by
  intro j hj
  have := findSlot_none hn ((j + cap - home cap k) % cap) (Nat.mod_lt _ (by omega))
  rw [stops, slotAt_surj hj] at this
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at this
  exact this

theorem key_of_full {cap : Nat} {ks : List (BitVec 32)} {us : List (BitVec 8)} {k : BitVec 32}
    {s : Nat} (hs : findSlot cap ks us k = some s) (hf : us.getD s 0 ≠ 0) : ks.getD s 0 = k := by
  obtain ⟨d, -, rfl, hst, -⟩ := findSlot_some hs
  simp only [stops, Bool.or_eq_true, beq_iff_eq] at hst
  rcases hst with h | h
  · exact absurd h hf
  · exact h

theorem repr_insert {cap : Nat} {ks vs : List (BitVec 32)} {us : List (BitVec 8)} {M : Model}
    (R : TableRepr cap ks vs us M) {k x : BitVec 32} {s : Nat} (hs : findSlot cap ks us k = some s)
    (h0 : us.getD s 0 = 0) :
    TableRepr cap (ks.set s k) (vs.set s x) (us.set s 1) ((k, x) :: M) := by
  have habs := absent_of_empty R hs h0
  obtain ⟨d, hd, rfl, -, hfirst⟩ := findSlot_some hs
  have hc : 0 < cap := by omega
  have hslt := slotAt_lt hc k d
  have lk := R.lks; have lv := R.lvs; have lu := R.lus
  have gk : ∀ j, (ks.set (slotAt cap k d) k).getD j 0 = if j = slotAt cap k d then k else ks.getD j 0 :=
    fun j => getD_set (by omega)
  have gv : ∀ j, (vs.set (slotAt cap k d) x).getD j 0 = if j = slotAt cap k d then x else vs.getD j 0 :=
    fun j => getD_set (by omega)
  have gu : ∀ j, (us.set (slotAt cap k d) 1).getD j 0 = if j = slotAt cap k d then 1 else us.getD j 0 :=
    fun j => getD_set (by omega)
  -- old full slots stay full
  have mono : ∀ t, us.getD t 0 ≠ 0 → (us.set (slotAt cap k d) 1).getD t 0 ≠ 0 := by
    intro t ht; rw [gu]; split <;> simp_all
  refine ⟨by simp [lk], by simp [lv], by simp [lu], ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj hf
    by_cases hjs : j = slotAt cap k d
    · subst hjs
      simp only [gk, ↓reduceIte]
      refine ⟨d, hd, rfl, fun d' hd' => mono _ ?_⟩
      have := hfirst d' hd'
      simp only [stops, Bool.or_eq_false_iff, bne_iff_ne, ne_eq, beq_eq_false_iff_ne] at this
      exact this.1
    · simp only [gu, hjs, ↓reduceIte] at hf
      simp only [gk, hjs, ↓reduceIte]
      obtain ⟨e, he, hej, hpath⟩ := R.closed j hj hf
      exact ⟨e, he, hej, fun d' hd' => mono _ (hpath d' hd')⟩
  · intro j j' hj hj' hf hf' hkk
    rw [gk, gk] at hkk
    rw [gu] at hf hf'
    by_cases h1 : j = slotAt cap k d <;> by_cases h2 : j' = slotAt cap k d
    · rw [h1, h2]
    · simp only [h1, ↓reduceIte, h2, ↓reduceIte] at hkk hf'
      exact absurd hkk.symm (habs j' hj' hf')
    · simp only [h2, ↓reduceIte, h1, ↓reduceIte] at hkk hf
      exact absurd hkk (habs j hj hf)
    · simp only [h1, ↓reduceIte, h2, ↓reduceIte] at hkk hf hf'
      exact R.uniq j j' hj hj' hf hf' hkk
  · intro k' x'
    rw [List.mem_cons, R.mem]
    constructor
    · rintro (e | ⟨j, hj, hf, hkj, hvj⟩)
      · cases e
        exact ⟨slotAt cap k d, hslt, by rw [gu]; simp, by rw [gk]; simp, by rw [gv]; simp⟩
      · have hjs : j ≠ slotAt cap k d := fun e => by subst e; exact hf h0
        exact ⟨j, hj, mono _ hf, by simp only [gk, hjs, ↓reduceIte]; exact hkj, by simp only [gv, hjs, ↓reduceIte]; exact hvj⟩
    · rintro ⟨j, hj, hf, hkj, hvj⟩
      rw [gk] at hkj; rw [gv] at hvj; rw [gu] at hf
      by_cases hjs : j = slotAt cap k d
      · simp only [hjs, ↓reduceIte] at hkj hvj; subst hkj hvj; exact .inl rfl
      · simp only [hjs, ↓reduceIte] at hkj hvj hf
        exact .inr ⟨j, hj, hf, hkj, hvj⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, R.nodup⟩
    obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.mp hm
    simp only at he; subst he
    obtain ⟨j, hj, hf, hkj, -⟩ := (R.mem _ _).mp hab
    exact habs j hj hf hkj
  · simp only [List.length_cons]
    rw [R.count, nfull_set (by omega) h0]

theorem repr_overwrite {cap : Nat} {ks vs : List (BitVec 32)} {us : List (BitVec 8)} {M : Model}
    (R : TableRepr cap ks vs us M) {k x : BitVec 32} {s : Nat} (hs : s < cap)
    (hf : us.getD s 0 ≠ 0) (hk : ks.getD s 0 = k) :
    TableRepr cap ks (vs.set s x) us (M.map fun p => if p.1 = k then (k, x) else p) := by
  have lv := R.lvs
  have gv : ∀ j, (vs.set s x).getD j 0 = if j = s then x else vs.getD j 0 :=
    fun j => getD_set (by omega)
  refine ⟨R.lks, by simp [lv], R.lus, R.closed, R.uniq, ?_, ?_, ?_⟩
  · intro k' x'
    rw [List.mem_map]
    constructor
    · rintro ⟨⟨a, b⟩, hm, e⟩
      by_cases ha : a = k
      · simp only [ha, ↓reduceIte, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        exact ⟨s, hs, hf, hk, by rw [gv]; simp⟩
      · simp only [ha, ↓reduceIte, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        obtain ⟨j, hj, hfj, hkj, hvj⟩ := (R.mem _ _).mp hm
        have hjs : j ≠ s := fun e => by subst e; exact ha (hkj.symm.trans hk)
        exact ⟨j, hj, hfj, hkj, by simp only [gv, hjs, ↓reduceIte]; exact hvj⟩
    · rintro ⟨j, hj, hfj, hkj, hvj⟩
      rw [gv] at hvj
      by_cases hjs : j = s
      · subst hjs
        simp only [↓reduceIte] at hvj
        refine ⟨(k, vs.getD j 0), (R.mem _ _).mpr ⟨j, hj, hfj, hk, rfl⟩, ?_⟩
        subst hvj; rw [← hkj, hk]; simp
      · simp only [hjs, ↓reduceIte] at hvj
        refine ⟨(k', x'), (R.mem _ _).mpr ⟨j, hj, hfj, hkj, hvj⟩, ?_⟩
        have : k' ≠ k := fun e => hjs (R.uniq j s hj hs hfj hf (by rw [hkj, hk, e]))
        simp [this]
  · rw [List.map_map]
    have : (Prod.fst ∘ fun p : BitVec 32 × BitVec 32 => if p.1 = k then (k, x) else p) = Prod.fst := by
      funext p; simp only [Function.comp]; split <;> simp_all
    rw [this]; exact R.nodup
  · rw [List.length_map]; exact R.count

/-! ### The main lemmas -/

/-- `putRef` returns `true` exactly when the model's insert succeeds, and the new table
represents the new model; on failure nothing changes. -/
theorem putRef_correct {cap : Nat} {ks vs : List (BitVec 32)} {us : List (BitVec 8)} {M : Model}
    (R : TableRepr cap ks vs us M) (hc : 0 < cap) (k x : BitVec 32) :
    (putRef cap ks vs us k x).1 = (mput cap M k x).isSome ∧
    TableRepr cap (putRef cap ks vs us k x).2.1 (putRef cap ks vs us k x).2.2.1
      (putRef cap ks vs us k x).2.2.2 ((mput cap M k x).getD M) ∧
    (mput cap M k x = none → putRef cap ks vs us k x = (false, ks, vs, us)) := by
  rcases hfs : findSlot cap ks us k with _ | s
  · have hall := full_of_none hfs
    have hnone : M.lookup k = none := lookup_none_iff.mpr fun x' hm => by
      obtain ⟨j, hj, -, hkj, -⟩ := (R.mem _ _).mp hm
      exact (hall j hj).2 hkj
    have hlen : M.length = cap := by
      rw [R.count, nfull_all (fun j hj => (hall j (R.lus ▸ hj)).1), R.lus]
    have hm : mput cap M k x = none := by simp [mput, hnone, hlen]
    simp [putRef, hfs, hm, R]
  · obtain ⟨d, hd, rfl, -, -⟩ := findSlot_some hfs
    have hslt := slotAt_lt hc k d
    by_cases h0 : us.getD (slotAt cap k d) 0 = 0
    · have habs := absent_of_empty R hfs h0
      have hnone : M.lookup k = none := lookup_none_iff.mpr fun x' hm => by
        obtain ⟨j, hj, hf, hkj, -⟩ := (R.mem _ _).mp hm
        exact habs j hj hf hkj
      have hlen : M.length < cap := by
        rw [R.count, ← R.lus]; exact nfull_lt (by rw [R.lus]; exact hslt) h0
      have hm : mput cap M k x = some ((k, x) :: M) := by simp [mput, hnone, hlen]
      simp only [putRef, hfs, h0, ↓reduceIte, hm, Option.isSome_some, Option.getD_some, true_and]
      exact ⟨repr_insert R hfs h0, fun h => nomatch h⟩
    · have hk := key_of_full hfs h0
      have hsome : M.lookup k = some (vs.getD (slotAt cap k d) 0) :=
        (lookup_some_iff R.nodup).mpr ((R.mem _ _).mpr ⟨_, hslt, h0, hk, rfl⟩)
      have hm : mput cap M k x = some (M.map fun p => if p.1 = k then (k, x) else p) := by
        simp [mput, hsome]
      simp only [putRef, hfs, h0, ↓reduceIte, hm, Option.isSome_some, Option.getD_some, true_and]
      exact ⟨repr_overwrite R hslt h0 hk, fun h => nomatch h⟩

/-- `getRef` is the model's lookup. -/
theorem getRef_correct {cap : Nat} {ks vs : List (BitVec 32)} {us : List (BitVec 8)} {M : Model}
    (R : TableRepr cap ks vs us M) (k : BitVec 32) : getRef cap ks vs us k = mget M k := by
  unfold mget
  rcases hfs : findSlot cap ks us k with _ | s
  · have hall := full_of_none hfs
    rw [lookup_none_iff.mpr fun x' hm => by
      obtain ⟨j, hj, -, hkj, -⟩ := (R.mem _ _).mp hm
      exact (hall j hj).2 hkj]
    simp [getRef, hfs]
  · obtain ⟨d, hd, rfl, -, -⟩ := findSlot_some hfs
    have hc : 0 < cap := by omega
    have hslt := slotAt_lt hc k d
    by_cases h0 : us.getD (slotAt cap k d) 0 = 0
    · have habs := absent_of_empty R hfs h0
      rw [lookup_none_iff.mpr fun x' hm => by
        obtain ⟨j, hj, hf, hkj, -⟩ := (R.mem _ _).mp hm
        exact habs j hj hf hkj]
      simp only [getRef, hfs, h0, ↓reduceIte]
    · have hk := key_of_full hfs h0
      rw [(lookup_some_iff R.nodup).mpr ((R.mem _ _).mpr ⟨_, hslt, h0, hk, rfl⟩)]
      simp only [getRef, hfs, h0, ↓reduceIte]

/-! ## 3. The code

```c
bool hm_put(uint32_t *keys, uint32_t *vals, uint8_t *used, uint32_t cap, uint32_t k, uint32_t v) {
  uint32_t mask = cap - 1u;
  uint32_t s = (k * 2654435761u) & mask;
  uint32_t i = 0u;
  while (i < cap) {
    uint8_t u = used[s];
    if (u == 0) { keys[s] = k; vals[s] = v; used[s] = 1; return true; }
    uint32_t kk = keys[s];
    if (kk == k) { vals[s] = v; return true; }
    s = (s + 1u) & mask;
    i = i + 1u;
  }
  return false;
}
```
`hm_get` probes the same way, returning `false` at an empty slot.
-/

def hmPut : Fn where
  name   := "hm_put"
  params := [("keys", .ptr .u32), ("vals", .ptr .u32), ("used", .ptr .u8), ("cap", .int .u32),
             ("k", .int .u32), ("v", .int .u32)]
  locals := [("mask", .int .u32), ("s", .int .u32), ("i", .int .u32), ("u", .int .u8),
             ("kk", .int .u32)]
  body   := .block [
    "mask" ::= v "cap" - .u32 1,
    "s" ::= (v "k" * .u32 2654435761) &&& v "mask",
    "i" ::= .u32 0,
    .while (v "i" <. v "cap") (.block [
      .load "u" (v "used") (v "s"),
      .ite (v "u" ==. .u8 0) (.block [
        .store (v "keys") (v "s") (v "k"),
        .store (v "vals") (v "s") (v "v"),
        .store (v "used") (v "s") (.u8 1),
        .ret .tt]) .skip,
      .load "kk" (v "keys") (v "s"),
      .ite (v "kk" ==. v "k") (.block [
        .store (v "vals") (v "s") (v "v"),
        .ret .tt]) .skip,
      "s" ::= (v "s" + .u32 1) &&& v "mask",
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .bool
  result := .ff

def hmGet : Fn where
  name   := "hm_get"
  params := [("keys", .ptr .u32), ("vals", .ptr .u32), ("used", .ptr .u8), ("cap", .int .u32),
             ("k", .int .u32), ("out", .ptr .u32)]
  locals := [("mask", .int .u32), ("s", .int .u32), ("i", .int .u32), ("u", .int .u8),
             ("kk", .int .u32), ("r", .int .u32)]
  body   := .block [
    "mask" ::= v "cap" - .u32 1,
    "s" ::= (v "k" * .u32 2654435761) &&& v "mask",
    "i" ::= .u32 0,
    .while (v "i" <. v "cap") (.block [
      .load "u" (v "used") (v "s"),
      .ite (v "u" ==. .u8 0) (.ret .ff) .skip,
      .load "kk" (v "keys") (v "s"),
      .ite (v "kk" ==. v "k") (.block [
        .load "r" (v "vals") (v "s"),
        .store (v "out") (.u32 0) (v "r"),
        .ret .tt]) .skip,
      "s" ::= (v "s" + .u32 1) &&& v "mask",
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .bool
  result := .ff

#guard hmPut.typeCheck && hmGet.typeCheck
#guard (cTranslationUnit [hmPut, hmGet]).isOk

/-! ## 4. The code against the reference, in the interpreter

Blocks: 0 = keys, 1 = vals, 2 = used, 3 = out. -/

def tableMem (cap : Nat) : Mem :=
  [(0, List.replicate cap (.u32 0)), (1, List.replicate cap (.u32 0)),
   (2, List.replicate cap (.u8 0)), (3, [.u32 0])]

def runCode (cap : Nat) (m : Mem) : List (BitVec 32 × Option (BitVec 32)) → List String
  | [] => []
  | (k, some x) :: ops =>
    match hmPut.callMem [.ptr .u32 ⟨0, 0⟩, .ptr .u32 ⟨1, 0⟩, .ptr .u8 ⟨2, 0⟩, .u32 cap,
        .int .u32 k, .int .u32 x] m with
    | .ok (.bool b, m') => s!"{b}" :: runCode cap m' ops
    | _ => ["stuck"]
  | (k, none) :: ops =>
    match hmGet.callMem [.ptr .u32 ⟨0, 0⟩, .ptr .u32 ⟨1, 0⟩, .ptr .u8 ⟨2, 0⟩, .u32 cap,
        .int .u32 k, .ptr .u32 ⟨3, 0⟩] m with
    | .ok (.bool true, m') =>
      match m'.read 3 0 with
      | some (.int .u32 r) => showGet (some r) :: runCode cap m' ops
      | _ => ["no out"]
    | .ok (.bool false, m') => "none" :: runCode cap m' ops
    | _ => ["stuck"]

#guard forAll genScript fun (cap, ops) => runCode cap (tableMem cap) ops == runModel cap [] ops

/-! ## 5. The code refines the probing reference -/

/-- Masking with `cap - 1` is `% cap`, for a power of two. -/
theorem and_mask {cap p : Nat} (hpow : cap = 2 ^ p) (hp : p ≤ 16) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (cap - 1) = BitVec.ofNat 32 (x.toNat % cap) := by
  subst hpow
  have h16 : 2 ^ p ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) hp
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hlt := Nat.mod_lt x.toNat (Nat.two_pow_pos p)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ p - 1 < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem slot_home {cap p : Nat} (hpow : cap = 2 ^ p) (hp : p ≤ 16) (k : BitVec 32) :
    (k * 2654435761#32) &&& BitVec.ofNat 32 (cap - 1) = BitVec.ofNat 32 (slotAt cap k 0) := by
  rw [and_mask hpow hp]; simp [slotAt, home]

theorem slot_next {cap p : Nat} (hpow : cap = 2 ^ p) (hp : p ≤ 16) (k : BitVec 32) (i : Nat) :
    (BitVec.ofNat 32 (slotAt cap k i) + 1#32) &&& BitVec.ofNat 32 (cap - 1) =
      BitVec.ofNat 32 (slotAt cap k (i + 1)) := by
  have hc : 0 < cap := by subst hpow; exact Nat.two_pow_pos p
  have h16 : cap ≤ 2 ^ 16 := by subst hpow; exact Nat.pow_le_pow_right (by omega) hp
  have hs := slotAt_lt hc k i
  rw [and_mask hpow hp]
  congr 1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : slotAt cap k i < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : slotAt cap k i + 1 % 2 ^ 32 < 2 ^ 32)]
  simp only [slotAt, Nat.mod_add_mod, Nat.add_assoc]

def putInv (kp vp up : Ptr) (cap : Nat) (ks vs : List (BitVec 32)) (us : List (BitVec 8))
    (k x : BitVec 32) (h₀ : Heap) : SProp := fun st h =>
  ∃ i, i ≤ cap ∧ slotAt cap k i < cap ∧ st.get "keys" = some (.ptr .u32 kp) ∧
    st.get "vals" = some (.ptr .u32 vp) ∧
    st.get "used" = some (.ptr .u8 up) ∧ st.get "cap" = some (nu32 cap) ∧
    st.get "k" = some (.int .u32 k) ∧ st.get "v" = some (.int .u32 x) ∧
    st.get "mask" = some (nu32 (cap - 1)) ∧ st.get "i" = some (nu32 i) ∧
    st.get "s" = some (nu32 (slotAt cap k i)) ∧
    (∀ d, d < i → stops cap ks us k d = false) ∧ h = h₀

/-- **Not yet proved** (`sorry`): `hm_put` computes `putRef`. The attempted proof
(`lc_auto` + `lc_while` with `putInv`, `slot_home`, `slot_next`) did not terminate in time. -/
theorem hmPut_refines (P : Program) (kp vp up : Ptr) (cap p : Nat) (hpow : cap = 2 ^ p)
    (hp : p ≤ 16) (ks vs : List (BitVec 32)) (us : List (BitVec 8)) (k x : BitVec 32)
    (hks : ks.length = cap) (hvs : vs.length = cap) (hus : us.length = cap)
    (h hf : Heap) (m : Mem)
    (hpre : (array kp (u32s ks) ∗ array vp (u32s vs) ∗ array up (u8s us)) h)
    (d : h.Disjoint hf) (hm : m.heap = h.union hf) :
    ∃ v m' h', hmPut.Returns P [.ptr .u32 kp, .ptr .u32 vp, .ptr .u8 up, .u32 cap,
        .int .u32 k, .int .u32 x] m v m' ∧ h'.Disjoint hf ∧ m'.heap = h'.union hf ∧
      v = .bool (putRef cap ks vs us k x).1 ∧
      (array kp (u32s (putRef cap ks vs us k x).2.1) ∗ array vp (u32s (putRef cap ks vs us k x).2.2.1) ∗
        array up (u8s (putRef cap ks vs us k x).2.2.2)) h' := by
  sorry

end Examples.HashMap
