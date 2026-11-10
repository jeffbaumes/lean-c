/-!
# `lake exe lc`: check one module, emit C, run the differential tests

```
lake exe lc check <module> [cases]     # build + #guards + proofs + axioms + hygiene + small difftest
lake exe lc emit [dir/name]            # write name.h + name.c for every example
lake exe lc difftest [cases] [seed] [fn | --module M]
lake exe lc ringtest [scripts] [seed]
```

## Why two executables

`emit`, `difftest` and `ringtest` need every example function, so they live in `lc-suite`
(Tools/Suite.lean), which imports `Tests`. This driver imports nothing from the project.
If it did, a broken proof in the module you are checking would stop `lc` itself from
building, and `check` could never report on it. So `lc` stays buildable whatever state the
examples are in, runs `lake build <module>` as a subprocess, and reads the messages.
The other commands are forwarded to `lake exe lc-suite`.

## What `check` reports

| Row | Passes when |
|---|---|
| `build` | `lake build <module>` succeeds (errors are split into the two rows below) |
| `#guard` | no `#guard` fails: type checks, interpreter runs, reference property tests |
| `proofs` | no other error, no `sorry` warning |
| `axioms` | every `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound` (and there is at least one) |
| `hygiene` | the source has no `sorry`, `admit`, `native_decide` or `axiom` outside comments |
| `difftest` | the module's functions in `Tests/Suite.lean` pass a small difftest (`nice -n 19`) |

The difftest runs only once everything else passes, since it needs the whole suite to build.
A module that declares no suite functions (a proofs-only module) skips it.
-/

namespace LcTool

/-! ## Running subprocesses -/

/-- The `lake` that launched us (`lake exe` sets `$LAKE`), else whatever is on `PATH`. -/
def lake : IO String := return (← IO.getEnv "LAKE").getD "lake"

def runCapture (cmd : String) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd, args }

/-- Run with inherited stdio and return the exit code. -/
def runInherit (cmd : String) (args : Array String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd, args }
  return (← child.wait)

/-! ## Lake's messages -/

inductive Sev where | error | warning | info
  deriving BEq

structure Msg where
  sev : Sev
  /-- `file:line:col`, or empty for messages without a position. -/
  pos : String
  text : String

/-- Split lake's output into messages. A message starts with `error:`, `warning:` or
`info:` and runs until the next one, or until a line of lake's own progress output. -/
def parseMsgs (out : String) : List Msg := Id.run do
  let mut msgs : Array Msg := #[]
  let mut cur : Option Msg := none
  for line in out.splitOn "\n" do
    let hdr : Option (Sev × String) :=
      if line.startsWith "error: " then some (.error, (line.drop 7).toString)
      else if line.startsWith "warning: " then some (.warning, (line.drop 9).toString)
      else if line.startsWith "info: " then some (.info, (line.drop 6).toString)
      else none
    let isLakeChrome := line.startsWith "✖" || line.startsWith "⚠" || line.startsWith "ℹ" ||
      line.startsWith "✔" || line.startsWith "trace:" || line.startsWith "Some required" ||
      line.startsWith "- " || line.startsWith "Build completed"
    match hdr with
    | some (sev, rest) =>
      if let some m := cur then msgs := msgs.push m
      -- `Examples/Foo.lean:3:0: text`: the position is the first three `:`-fields
      let parts := rest.splitOn ": "
      let (pos, text) := match parts with
        | p :: t => if (p.splitOn ":").length == 3 && (p.splitOn ".lean:").length == 2
            then (p, ": ".intercalate t) else ("", rest)
        | [] => ("", rest)
      cur := some { sev, pos, text }
    | none =>
      if isLakeChrome then
        if let some m := cur then msgs := msgs.push m
        cur := none
      else if let some m := cur then
        cur := some { m with text := m.text ++ "\n" ++ line }
  if let some m := cur then msgs := msgs.push m
  return msgs.toList

def Msg.isGuardFailure (m : Msg) : Bool :=
  m.sev == .error && (m.text.splitOn "did not evaluate to `true`").length > 1

def Msg.isSorry (m : Msg) : Bool :=
  m.sev == .warning && (m.text.splitOn "declaration uses `sorry`").length > 1

/-- The axioms in a `#print axioms` message: `some []` for "does not depend on any axioms". -/
def Msg.axioms (m : Msg) : Option (String × List String) :=
  if m.sev != .info then none else
  match m.text.splitOn "' depends on axioms: [" with
  | [pre, post] =>
    let names := ((post.splitOn "]")[0]!.splitOn ",").map (·.trimAscii.toString) |>.filter (· ≠ "")
    some ((pre.drop 1).toString, names)
  | _ =>
    match m.text.splitOn "' does not depend on any axioms" with
    | [pre, _] => some ((pre.drop 1).toString, [])
    | _ => none

def allowedAxioms : List String := ["propext", "Classical.choice", "Quot.sound"]

/-! ## Scanning the source -/

/-- Blank out comments and string literals (keeping line structure), so the token scan
below doesn't trip over prose like "no `sorry`" in a docstring. Block comments nest. -/
def stripComments (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := #[]
  let mut i := 0
  let mut depth := 0
  let mut inStr := false
  let mut inLine := false
  while i < cs.size do
    let c := cs[i]!
    let n := cs[i+1]?.getD ' '
    if inLine then
      if c == '\n' then inLine := false; out := out.push c else out := out.push ' '
      i := i + 1
    else if depth > 0 then
      if c == '/' && n == '-' then depth := depth + 1; out := out ++ #[' ', ' ']; i := i + 2
      else if c == '-' && n == '/' then depth := depth - 1; out := out ++ #[' ', ' ']; i := i + 2
      else out := out.push (if c == '\n' then c else ' '); i := i + 1
    else if inStr then
      if c == '\\' then out := out ++ #[' ', ' ']; i := i + 2
      else
        if c == '"' then inStr := false
        out := out.push (if c == '\n' then c else ' '); i := i + 1
    else if c == '/' && n == '-' then depth := 1; out := out ++ #[' ', ' ']; i := i + 2
    else if c == '-' && n == '-' then inLine := true; out := out ++ #[' ', ' ']; i := i + 2
    else if c == '"' then inStr := true; out := out.push ' '; i := i + 1
    else out := out.push c; i := i + 1
  return String.ofList out.toList

def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || c == '.' || c == '#' || c == '!' || c == '?'

/-- Tokens of a line: maximal runs of identifier characters (so `#guard` and `#print` are tokens). -/
def tokens (line : String) : List String :=
  (line.split (fun c => !isIdChar c)).toList.map (·.toString) |>.filter (· ≠ "")

structure Scan where
  guards : Nat := 0
  theorems : Nat := 0
  printAxioms : Nat := 0
  /-- `(line, token)` for each forbidden token. -/
  forbidden : List (Nat × String) := []

def scanSource (src : String) : Scan := Id.run do
  let mut sc : Scan := {}
  for (line, k) in (stripComments src).splitOn "\n" |>.zipIdx do
    let ts := tokens line
    sc := { sc with
      guards := sc.guards + (ts.filter (· == "#guard")).length
      theorems := sc.theorems + (ts.filter (fun t => t == "theorem" || t == "lemma")).length
      printAxioms := sc.printAxioms + (ts.filter (· == "#print")).length }
    for t in ts do
      if t == "sorry" || t == "admit" || t == "native_decide" || t == "axiom" then
        sc := { sc with forbidden := sc.forbidden ++ [(k + 1, t)] }
  return sc

/-! ## The report -/

structure Row where
  name : String
  ok : Option Bool   -- `none`: skipped
  detail : String

def Row.render (r : Row) : String :=
  let status := match r.ok with | some true => "ok  " | some false => "FAIL" | none => "skip"
  s!"  {r.name.pushn ' ' (10 - r.name.length)}{status}  {r.detail}"

/-- First `n` lines of a message, indented. -/
def excerpt (m : Msg) (n : Nat := 6) : String :=
  let lines := m.text.splitOn "\n"
  let shown := lines.take n
  let more := if lines.length > n then s!"\n      … ({lines.length - n} more lines)" else ""
  let loc := if m.pos.isEmpty then "" else m.pos ++ ": "
  s!"    {loc}" ++ "\n      ".intercalate shown ++ more

/-- `Examples/Foo.lean` or `Examples.Foo` → (`Examples.Foo`, `Examples/Foo.lean`). -/
def resolveModule (arg : String) : String × String :=
  if arg.endsWith ".lean" then
    let m := ((arg.dropEnd 5).toString.replace "/" ".")
    (if m.startsWith "./" then (m.drop 2).toString else m, arg)
  else (arg, arg.replace "." "/" ++ ".lean")

def check (arg : String) (cases : Nat) : IO UInt32 := do
  let (mod, path) := resolveModule arg
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"lc check: no file {path} for module {mod}"
    return 2
  let lk ← lake
  IO.println s!"lc check {mod}"
  let mut rows : Array Row := #[]
  let mut problems : Array String := #[]

  -- 1. the source scan (cheap, and independent of whether it builds)
  let sc := scanSource (← IO.FS.readFile path)

  -- 2. lake build: type checking, #guards, proofs, #print axioms
  let t0 ← IO.monoMsNow
  let out ← runCapture lk #["build", mod]
  let secs := ((← IO.monoMsNow) - t0) / 100
  let elapsed := s!"{secs / 10}.{secs % 10}s"
  let msgs := parseMsgs (out.stdout ++ "\n" ++ out.stderr)
  let errors := msgs.filter (·.sev == .error)
  -- lake's own "build failed" summary line has no position and adds nothing
  let errors := errors.filter fun m => !(m.pos.isEmpty && m.text.trimAscii.toString == "build failed")
  let guardFails := errors.filter (·.isGuardFailure)
  let otherErrs := errors.filter (!·.isGuardFailure)
  let sorries := msgs.filter (·.isSorry)
  let built := out.exitCode == 0
  rows := rows.push {
    name := "build", ok := built,
    detail := if built then elapsed else s!"{errors.length} error(s), {elapsed}" }
  -- errors outside this file mean an import is broken: say so plainly
  let foreign := otherErrs.filter fun m => !m.pos.isEmpty && !m.pos.startsWith path
  if !foreign.isEmpty then
    problems := problems.push s!"  errors in imported modules (fix those first):"
  rows := rows.push {
    name := "#guard", ok := guardFails.isEmpty,
    detail := if guardFails.isEmpty then
        (if built then s!"{sc.guards} passed" else s!"{guardFails.length} failed so far (build stopped early?)")
      else s!"{guardFails.length} of {sc.guards} failed" }
  rows := rows.push {
    name := "proofs", ok := otherErrs.isEmpty && sorries.isEmpty,
    detail := if otherErrs.isEmpty && sorries.isEmpty then s!"{sc.theorems} theorems"
      else s!"{otherErrs.length} error(s), {sorries.length} sorry" }
  for m in guardFails ++ otherErrs ++ sorries do
    problems := problems.push (excerpt m)

  -- 3. axioms
  let axs := (msgs.filter (·.pos.startsWith path)).filterMap (·.axioms)
  let bad := axs.filter fun (_, as) => as.any (!allowedAxioms.contains ·)
  let axRow : Row :=
    if !bad.isEmpty then
      {
        name := "axioms", ok := false,
        detail := ", ".intercalate (bad.map fun (n, as) =>
          s!"{n} uses {", ".intercalate (as.filter (!allowedAxioms.contains ·))}") }
    else if axs.isEmpty then
      if sc.theorems == 0 then { name := "axioms", ok := none, detail := "no theorems" }
      else if !built then { name := "axioms", ok := none, detail := "not reached" }
      else {
             name := "axioms", ok := false,
             detail := s!"{sc.theorems} theorems but no #print axioms (end the file with one per main theorem)" }
    else { name := "axioms", ok := true, detail := s!"{axs.length} checked, standard only" }
  rows := rows.push axRow

  -- 4. hygiene
  rows := rows.push {
    name := "hygiene", ok := sc.forbidden.isEmpty,
    detail := if sc.forbidden.isEmpty then "no sorry / admit / native_decide / axiom"
      else ", ".intercalate (sc.forbidden.take 5 |>.map fun (l, t) => s!"{t} at line {l}") }

  -- 5. difftest, only when everything above passed
  let allOk := rows.all (·.ok != some false)
  if cases == 0 then
    rows := rows.push { name := "difftest", ok := none, detail := "skipped (cases = 0)" }
  else if !allOk then
    rows := rows.push { name := "difftest", ok := none, detail := "skipped until the above pass" }
  else
    let ls ← runCapture lk #["-q", "exe", "lc-suite", "list"]
    if ls.exitCode != 0 then
      let ms := (parseMsgs (ls.stdout ++ "\n" ++ ls.stderr)).filter (·.sev == .error)
      rows := rows.push {
        name := "difftest", ok := false,
        detail := "the suite (Tests/Suite.lean and every example) doesn't build" }
      for m in ms.take 3 do problems := problems.push (excerpt m)
    else
      let fns := (ls.stdout.splitOn "\n").filterMap fun l =>
        match l.splitOn " " with | [f, m] => if m == mod then some f else none | _ => none
      if fns.isEmpty then
        let hint := if (← IO.FS.readFile path).contains ": Fn" then
          " (it seems to define a Fn: add it to difftestFns in Tests/Suite.lean)" else ""
        rows := rows.push { name := "difftest", ok := none, detail := s!"no suite functions{hint}" }
      else
        let dt ← runCapture "nice" #["-n", "19", lk, "-q", "exe", "lc-suite", "difftest",
          toString cases, "1", "--module", mod]
        let lines := (dt.stdout.splitOn "\n").filter (· ≠ "")
        let ok := dt.exitCode == 0
        rows := rows.push {
          name := "difftest", ok := ok,
          detail := s!"{", ".intercalate fns}: {cases} random cases each, C (UBSan/ASan, -O2) vs. interpreter" }
        if !ok then
          problems := problems.push s!"  difftest output (rerun: nice -n 19 lake exe lc difftest {cases} 1 --module {mod}):"
          for l in (lines.drop 2) do problems := problems.push s!"    {l}"
          if !dt.stderr.isEmpty then problems := problems.push s!"    {dt.stderr.take 600}"

  for r in rows do IO.println r.render
  if !problems.isEmpty then
    IO.println "\nproblems:"
    for p in problems.toList.take 40 do IO.println p
    if problems.size > 40 then IO.println s!"  … and {problems.size - 40} more"
  let pass := rows.all (·.ok != some false)
  IO.println (if pass then "PASS" else "FAIL")
  return if pass then 0 else 1

def usage : String :=
  "usage: lc check <module | file.lean> [cases]\n" ++
  "       lc emit [dir/name] | lc difftest [cases] [seed] [fn | --module M] | lc ringtest [scripts] [seed]"

end LcTool

open LcTool in
def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: m :: rest =>
    let cases := (rest[0]? >>= String.toNat?).getD 30
    check m cases
  | cmd :: _ =>
    if ["emit", "difftest", "ringtest", "list"].contains cmd then
      runInherit (← lake) (#["-q", "exe", "lc-suite"] ++ args.toArray)
    else IO.println usage; return 2
  | [] => IO.println usage; return 2
