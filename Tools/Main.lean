import LC
import Examples

/-!
# `lake exe lc`: emit C, and differentially test it against the interpreter

```
lake exe lc emit [out.c]               # print every example as one C translation unit
lake exe lc difftest [cases] [seed] [fn]   # random inputs → interpreter vs. compiled C
lake exe lc ringtest [scripts] [seed]      # ring buffer: model vs. interpreter vs. compiled C
```

## How the differential test works (design §7)

For each function `f` and each random input `(args, mem)`:

1. Run the **interpreter** (`Fn.callMem`, proved sound in M1/M3).
   * `ok (v, mem')`: an expected output line.
   * `stuck`: this input has **UB**. It is *never* run as a normal test, because C may
     do anything. It goes into the "UB oracle" pass below.
   * `outOfFuel`: skipped.
2. Print `f` with the C printer. Generate a `main` that sets up each case's memory as
   arrays, calls `f`, and prints the result and the final memory in the same format
   the Lean side uses.
3. Compile twice: `-O1 -fsanitize=undefined,address` (UB caught at runtime) and `-O2`
   with no sanitizers (the optimiser is free to exploit any UB we accidentally emit).
   Both use `-std=c11 -Wall -Wextra -Werror -pedantic`.
4. Compare output line by line. **Any difference is a bug** in the printer, or in the
   semantics' model of C.
5. **UB oracle:** each stuck case runs alone in the sanitised binary. A sanitizer report
   means C agrees it's UB. Silence isn't a failure (not every UB is detectable, and
   LC is stricter than C in places), but the counts are informative.
-/

open LC

/-! ## A tiny PRNG (xorshift64): deterministic and dependency-free -/

structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next; (x.toNat % (max n 1), r)

/-- Random integer of type `t`, biased toward edge cases: 0, 1, −1, min, max, small. -/
def genInt (t : IntTy) (r : Rng) : Val × Rng :=
  let (k, r) := r.below 8
  let (x, r) := r.next
  let z : Int := match k with
    | 0 => 0 | 1 => 1 | 2 => -1 | 3 => t.min | 4 => t.max
    | 5 => x.toNat % 10 | 6 => x.toNat % 300
    | _ => x.toNat
  (Val.ofInt t z, r)

/-- A test case: arguments, plus memory with each block's element type. -/
structure Case where
  args : List Val
  blocks : List (Nat × IntTy × List Val)

def Case.mem (c : Case) : Mem := c.blocks.map fun (b, _, cs) => (b, cs)

/-- Random arguments. Each pointer gets its own block (length 1–8, random contents,
random offset), except that with probability 1/4 two pointers of the same type share
block 0, to test aliasing. -/
def genCase (f : Fn) (r : Rng) : Case × Rng := Id.run do
  let mut r := r
  let mut args : List Val := []
  let mut blocks : List (Nat × IntTy × List Val) := []
  for (_, ty) in f.params do
    match ty with
    | .ptr t =>
      let (share, r1) := r.below 4; r := r1
      let existing := blocks.find? fun (_, t', _) => t' == t
      match share, existing with
      | 0, some (b, _, cs) =>
        let (off, r2) := r.below cs.length; r := r2
        args := args ++ [.ptr t ⟨b, off⟩]
      | _, _ =>
        let (len, r2) := r.below 8; r := r2
        let len := len + 1
        let mut cs := []
        for _ in [0:len] do
          let (v, r3) := genInt t r; r := r3
          cs := cs ++ [v]
        let (z, r4) := r.below 3; r := r4
        let off := if z == 0 then (r.below len).1 else 0
        let b := blocks.length
        blocks := blocks ++ [(b, t, cs)]
        args := args ++ [.ptr t ⟨b, off⟩]
    | .int t =>
      -- lengths/counts: half the time a small number, so loops terminate in bounds
      let (small, r1) := r.below 2; r := r1
      if small == 0 && !t.signed then
        let (n, r2) := r.below 10; r := r2
        args := args ++ [Val.ofInt t n]
      else
        let (v, r2) := genInt t r; r := r2
        args := args ++ [v]
    | .bool =>
      let (b, r1) := r.below 2; r := r1
      args := args ++ [.bool (b == 1)]
    | .unit => args := args ++ [.unit]
  return (⟨args, blocks⟩, r)

/-! ## Expected output (Lean side) and the C harness -/

def showMem (m : Mem) : String :=
  " ".intercalate (m.map fun (b, cs) => s!"b{b}=[{", ".intercalate (cs.map toString)}]")

def expectedLine (k : Nat) (v : Val) (m : Mem) : String :=
  s!"case {k}: {v}" ++ (if m.isEmpty then "" else " " ++ showMem m)

/-- C statements printing a value of LC type `t` held in C expression `e`, in `Val.toString` format. -/
def cPrint (t : Ty) (e : String) : String :=
  match t with
  | .int it =>
    if it.signed then s!"printf(\"%lld{if it.signed then "i" else "u"}{it.bits}\", (long long)({e}));"
    else s!"printf(\"%lluu{it.bits}\", (unsigned long long)({e}));"
  | .bool => s!"printf(\"%s\", ({e}) ? \"true\" : \"false\");"
  | .unit => "printf(\"()\");"
  | .ptr _ => "printf(\"<ptr>\");"

def cArg : Val → Except String String
  | .ptr _ p => .ok s!"(b{p.blk} + {p.off})"
  | v => cValLit v

/-- One case as a C block: declare arrays, call, print. OK cases run when no selector
is given; stuck (UB) cases run only when selected individually. -/
def cCase (f : Fn) (k : Nat) (c : Case) (isOk : Bool) : Except String String := do
  -- Blocks live on the heap: ASan's heap redzones catch out-of-bounds accesses far more
  -- reliably than its stack instrumentation (which missed a 16-element overread here).
  let decls ← c.blocks.mapM fun (b, t, cs) => do
    let lits ← cs.mapM cValLit
    let tn := IntTy.cName t
    let inits := String.join ((lits.zipIdx).map fun (l, j) => s!" b{b}[{j}] = {l};")
    return s!"    {tn} *b{b} = malloc({cs.length} * sizeof({tn}));{inits}\n"
  let args ← c.args.mapM cArg
  let call := s!"{f.name}({", ".intercalate args})"
  let callStmt := match f.ret with
    | .unit => s!"    {call}; printf(\"case {k}: ()\");\n"
    | t => s!"    {cDecl t "r"} = {call};\n    printf(\"case {k}: \"); {cPrint t "r"}\n"
  let prints := c.blocks.map fun (b, t, cs) =>
    let items := (List.range cs.length).map fun j => cPrint (.int t) s!"b{b}[{j}]"
    s!"    printf(\" b{b}=[\"); " ++ " printf(\", \"); ".intercalate items ++ " printf(\"]\");\n"
  let frees := String.join (c.blocks.map fun (b, _, _) => s!"    free(b{b});\n")
  let guard := if isOk then s!"sel < 0 || sel == {k}" else s!"sel == {k}"
  return s!"  if ({guard}) \{\n{String.join decls}{callStmt}{String.join prints}    printf(\"\\n\");\n{frees}  }\n"

def harness (f : Fn) (okCases stuckCases : List (Nat × Case)) : Except String String := do
  let tu ← cTranslationUnit [f]
  let body ← (okCases.map (·, true) ++ stuckCases.map (·, false)).mapM fun ((k, c), ok) =>
    cCase f k c ok
  return tu ++ "\n#include <stdio.h>\n#include <stdlib.h>\n\n" ++
    "int main(int argc, char **argv) {\n  int sel = argc > 1 ? atoi(argv[1]) : -1;\n" ++
    String.join body ++ "  return 0;\n}\n"

/-! ## Driver -/

/-- The system C compiler. Not plain `clang`: under `lake exe`, Lean's own bundled
clang (which has no system headers) comes first on `PATH`. Override with `$LC_CC`. -/
def cc : IO String := do
  return (← IO.getEnv "LC_CC").getD "cc"

def compile (src out : String) (flags : List String) : IO (Option String) := do
  let r ← IO.Process.output { cmd := ← cc, args := (#["-std=c11", "-Wall", "-Wextra", "-Werror",
    "-pedantic", "-Wno-unused-parameter", "-o", out, src] ++ flags.toArray) }
  return if r.exitCode == 0 then none else some r.stderr

structure Stats where
  ok : Nat := 0
  stuck : Nat := 0
  fuel : Nat := 0
  mismatches : List String := []
  flagged : Nat := 0
  unflagged : List Nat := []

def sanFlags : List String := ["-O1", "-g", "-fsanitize=undefined,address", "-fno-sanitize-recover=all"]

def testFn (dir : String) (f : Fn) (n : Nat) (r : Rng) : IO (Stats × Rng) := do
  let mut r := r
  let mut st : Stats := {}
  let mut okCases : List (Nat × Case) := []
  let mut stuckCases : List (Nat × Case) := []
  let mut expected : List String := []
  for k in [0:n] do
    let (c, r') := genCase f r; r := r'
    match f.callMem c.args c.mem 20000 with
    | .ok (v, m') =>
      st := { st with ok := st.ok + 1 }
      okCases := okCases ++ [(k, c)]
      expected := expected ++ [expectedLine k v m']
    | .stuck => st := { st with stuck := st.stuck + 1 }; stuckCases := stuckCases ++ [(k, c)]
    | .outOfFuel => st := { st with fuel := st.fuel + 1 }
  let src := s!"{dir}/{f.name}.c"
  match harness f okCases stuckCases with
  | .error e => return ({ st with mismatches := [s!"printer error: {e}"] }, r)
  | .ok code => IO.FS.writeFile src code
  for (tag, flags) in [("san", sanFlags), ("O2", ["-O2"])] do
    let bin := s!"{dir}/{f.name}.{tag}"
    if let some err ← compile src bin flags then
      return ({ st with mismatches := [s!"[{tag}] compile failed:\n{err}"] }, r)
    -- one run executes every OK case (stuck cases are guarded by an explicit selector)
    let out ← IO.Process.output { cmd := bin, args := #[] }
    let got := (out.stdout.splitOn "\n").filter (· ≠ "")
    if out.exitCode != 0 then
      st := { st with mismatches := st.mismatches ++ [s!"[{tag}] exit {out.exitCode}: {out.stderr.take 400}"] }
    for (exp, g) in expected.zip got do
      if exp != g then
        st := { st with mismatches := st.mismatches ++ [s!"[{tag}]\n    expected: {exp}\n    got:      {g}"] }
    if got.length != expected.length then
      st := { st with mismatches := st.mismatches ++
        [s!"[{tag}] {got.length} output lines, expected {expected.length}"] }
  -- UB oracle: stuck cases (up to 20) under sanitizers, one process each
  for (k, _) in stuckCases.take 20 do
    let out ← IO.Process.output { cmd := s!"{dir}/{f.name}.san", args := #[toString k] }
    if out.exitCode != 0 && ((out.stderr.splitOn "runtime error").length > 1 ||
        (out.stderr.splitOn "AddressSanitizer").length > 1) then
      st := { st with flagged := st.flagged + 1 }
    else st := { st with unflagged := st.unflagged ++ [k] }
  return (st, r)

def difftest (n seed : Nat) (only : Option String) : IO UInt32 := do
  let dir := ".lake/difftest"
  IO.FS.createDirAll dir
  let mut r : Rng := ⟨(seed.toUInt64 * 0x9E3779B97F4A7C15) ||| 1⟩
  let mut failures := 0
  IO.println s!"difftest: {n} random cases per function, seed {seed}"
  IO.println s!"{"function".pushn ' ' 10} ok  stuck(flagged)  fuel  result"
  let fns := Examples.M4.all ++ [Examples.M5.rbPush, Examples.M5.rbPop]
  for f in fns.filter (fun f => only.all (· == f.name)) do
    let (st, r') ← testFn dir f n r; r := r'
    let verdict := if st.mismatches.isEmpty then "PASS" else "FAIL"
    if !st.mismatches.isEmpty then failures := failures + 1
    IO.println s!"{f.name.pushn ' ' (18 - f.name.length)} {st.ok}  {st.stuck}({st.flagged}/{min st.stuck 20})  {st.fuel}  {verdict}"
    for msg in st.mismatches.take 3 do IO.println s!"    {msg}"
    if !st.unflagged.isEmpty then
      IO.println s!"    UB not flagged by sanitizers for cases {st.unflagged} (run .lake/difftest/{f.name}.san <case>)"
  IO.println (if failures == 0 then "ALL PASS" else s!"{failures} function(s) FAILED")
  return if failures == 0 then 0 else 1

/-! ## `lc ringtest`: the ring buffer against the *abstract* queue model

The difftest compares C with the interpreter. Here the oracle is the specification itself,
a plain `List` used as a queue, which is what `rbPush_correct`/`rbPop_correct` say the code
implements. Each random script of operations runs three ways: the model, the interpreter
(chained `callMem`s), and compiled C under sanitizers and -O2. All three must agree. -/

/-- `some x` = push x, `none` = pop. -/
abbrev Op := Option Nat

def modelRun (cap : Nat) : List Nat → List Op → List String
  | _, [] => []
  | q, some x :: ops =>
    if q.length < cap then s!"push {x}: true" :: modelRun cap (q ++ [x]) ops
    else s!"push {x}: false" :: modelRun cap q ops
  | [], none :: ops => "pop: empty" :: modelRun cap [] ops
  | a :: q, none :: ops => s!"pop: {a}u8" :: modelRun cap q ops

def interpRun (cap : Nat) (m : Mem) : List Op → List String
  | [] => []
  | some x :: ops =>
    match Examples.M5.rbPush.callMem [.ptr .u8 ⟨0, 0⟩, .ptr .u32 ⟨1, 0⟩, Val.ofInt .u32 cap,
        Val.ofInt .u8 x] m with
    | .ok (.bool b, m') => s!"push {x}: {b}" :: interpRun cap m' ops
    | _ => ["push: interpreter stuck"]
  | none :: ops =>
    match Examples.M5.rbPop.callMem [.ptr .u8 ⟨0, 0⟩, .ptr .u32 ⟨1, 0⟩, Val.ofInt .u32 cap,
        .ptr .u8 ⟨2, 0⟩] m with
    | .ok (.bool true, m') =>
      match m'.read 2 0 with
      | some w => s!"pop: {w}" :: interpRun cap m' ops
      | none => ["pop: no out"]
    | .ok (.bool false, m') => "pop: empty" :: interpRun cap m' ops
    | _ => ["pop: interpreter stuck"]

def genScript (r : Rng) (len : Nat) : List Op × Rng := Id.run do
  let mut r := r
  let mut ops := []
  for _ in [0:len] do
    let (k, r1) := r.below 2; r := r1
    let (x, r2) := r.below 256; r := r2
    ops := ops ++ [if k == 0 then some x else none]
  return (ops, r)

def cScript (k cap : Nat) (ops : List Op) : String :=
  let calls := ops.map fun
    | some x => s!"    ok = rb_push(buf, st, {cap}u, (uint8_t){x}u); printf(\"push {x}: %s\\n\", ok ? \"true\" : \"false\");\n"
    | none => "    ok = rb_pop(buf, st, " ++ toString cap ++ "u, out); if (ok) printf(\"pop: %uu8\\n\", (unsigned)out[0]); else printf(\"pop: empty\\n\");\n"
  s!"  if (sel < 0 || sel == {k}) \{\n    uint8_t *buf = malloc({cap}); uint32_t *st = malloc(2 * sizeof(uint32_t)); uint8_t *out = malloc(1);\n" ++
  s!"    st[0] = 0u; st[1] = 0u; bool ok;\n" ++ String.join calls ++
  "    free(buf); free(st); free(out);\n  }\n"

def ringtest (nScripts seed : Nat) : IO UInt32 := do
  let dir := ".lake/ringtest"
  IO.FS.createDirAll dir
  let mut r : Rng := ⟨(seed.toUInt64 * 0x9E3779B97F4A7C15) ||| 1⟩
  let mut expected : List String := []
  let mut cases : List String := []
  let mut interpMismatch := 0
  for k in [0:nScripts] do
    let (c, r1) := r.below 6; r := r1
    let cap := c + 1
    let (ops, r2) := genScript r 40; r := r2
    let model := modelRun cap [] ops
    let mem0 : Mem := [(0, List.replicate cap (Val.ofInt .u8 0)), (1, [Val.ofInt .u32 0, Val.ofInt .u32 0]),
      (2, [Val.ofInt .u8 0])]
    if interpRun cap mem0 ops != model then interpMismatch := interpMismatch + 1
    expected := expected ++ model
    cases := cases ++ [cScript k cap ops]
  let tu ← match cTranslationUnit [Examples.M5.rbPush, Examples.M5.rbPop] with
    | .ok t => pure t
    | .error e => IO.eprintln e; return 1
  let src := s!"{dir}/ring.c"
  IO.FS.writeFile src (tu ++ "\n#include <stdio.h>\n#include <stdlib.h>\n\nint main(int argc, char **argv) {\n" ++
    "  int sel = argc > 1 ? atoi(argv[1]) : -1;\n" ++ String.join cases ++ "  return 0;\n}\n")
  let mut fails := 0
  IO.println s!"ringtest: {nScripts} random scripts × 40 ops, capacities 1–6, seed {seed}"
  IO.println s!"  interpreter vs model: {nScripts - interpMismatch}/{nScripts} scripts agree"
  if interpMismatch > 0 then fails := fails + 1
  for (tag, flags) in [("san", sanFlags), ("O2", ["-O2"])] do
    let bin := s!"{dir}/ring.{tag}"
    if let some err ← compile src bin flags then
      IO.println s!"  [{tag}] compile failed:\n{err}"; return 1
    let out ← IO.Process.output { cmd := bin, args := #[] }
    let got := (out.stdout.splitOn "\n").filter (· ≠ "")
    let bad := (expected.zip got).filter (fun (e, g) => e != g)
    let ok := out.exitCode == 0 && bad.isEmpty && got.length == expected.length
    IO.println s!"  compiled C [{tag}] vs model: {if ok then "PASS" else "FAIL"} ({got.length}/{expected.length} lines)"
    for (e, g) in bad.take 3 do IO.println s!"    expected {e}, got {g}"
    if !ok then
      IO.println s!"    {out.stderr.take 400}"
      fails := fails + 1
  IO.println (if fails == 0 then "ALL PASS" else "FAILED")
  return if fails == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "emit" :: rest =>
    match cTranslationUnit (Examples.M4.all ++ [Examples.M5.rbPush, Examples.M5.rbPop]) with
    | .error e => IO.eprintln e; return 1
    | .ok code =>
      match rest with
      | [path] => IO.FS.writeFile path code; IO.println s!"wrote {path}"
      | _ => IO.print code
      return 0
  | "difftest" :: rest =>
    let n := (rest[0]? >>= String.toNat?).getD 200
    let seed := (rest[1]? >>= String.toNat?).getD 1
    difftest n seed rest[2]?
  | "ringtest" :: rest =>
    let n := (rest[0]? >>= String.toNat?).getD 200
    let seed := (rest[1]? >>= String.toNat?).getD 1
    ringtest n seed
  | _ => IO.println "usage: lc emit [out.c] | lc difftest [cases] [seed] [function] | lc ringtest [scripts] [seed]"; return 2
