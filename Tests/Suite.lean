import Examples
import Tests.PrinterStress

/-!
# The differential-test suite

Every function `lake exe lc difftest` runs against the interpreter. Each entry records the
module that declares the function, so `lake exe lc check <module>` can difftest just that
module's functions. `suite_entry% f` fills the module in at elaboration time, so it can't
go stale.
-/

open LC

namespace Tests

/-- A function under test, the program it runs in (its callees), and its declaring module. -/
structure Entry where
  fn : Fn
  prog : Program := []
  module : String

open Lean Elab Term in
/-- `module_of% c`: the name of the module that declares constant `c`, as a string. -/
elab "module_of% " id:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let some idx := env.getModuleIdxFor? n
    | throwError "module_of%: {n} is declared in this file"
  return toExpr (env.header.moduleNames[idx.toNat]!).toString

/-- `suite_entry% f` or `suite_entry% f in P`: an `Entry` for `f`, tagged with its module. -/
syntax "suite_entry% " ident (" in " term)? : term
macro_rules
  | `(suite_entry% $f) => `({ fn := $f, module := module_of% $f : Entry })
  | `(suite_entry% $f in $P) => `({ fn := $f, prog := $P, module := module_of% $f : Entry })

def difftestFns : List Entry :=
  [suite_entry% Examples.SumTo.sumTo,
   suite_entry% Examples.Arith.gcd,
   suite_entry% Examples.Arith.popcount,
   suite_entry% Examples.Arith.sub32,
   suite_entry% Examples.Arith.sub32u,
   suite_entry% Examples.Arith.safeDivGt1,
   suite_entry% Examples.ArraySum.arraySum,
   suite_entry% Examples.Copy.copy,
   suite_entry% Examples.Hash.fnv1a,
   suite_entry% Examples.RingBuffer.rbPush,
   suite_entry% Examples.RingBuffer.rbPop,
   suite_entry% Examples.Search.findFirst,
   suite_entry% Examples.Search.lowerBound,
   suite_entry% Examples.SpecFirst.isSorted,
   suite_entry% Examples.Crc32.crc32,
   suite_entry% Examples.Utf8.utf8Valid]
  ++ Tests.PrinterStress.all.map (fun f => { fn := f, module := "Tests.PrinterStress" })
  ++ [suite_entry% Examples.ParseU32.isDigit in Examples.ParseU32.prog,
      suite_entry% Examples.ParseU32.parseU32 in Examples.ParseU32.prog]

#guard (difftestFns.find? (·.fn.name == "gcd")).map (·.module) == some "Examples.Arith"

/-- Every function, once (for `lc emit`). -/
def allFns : List Fn :=
  difftestFns.map (·.fn)

#guard (cTranslationUnit allFns).isOk

end Tests
