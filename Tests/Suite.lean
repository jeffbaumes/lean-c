import Examples
import Tests.PrinterStress

/-!
# The differential-test suite

Every function `lake exe lc difftest` runs against the interpreter.
-/

open LC

namespace Tests

/-- Each entry: the function under test, and the program it runs in (its callees). -/
def difftestFns : List (Fn × Program) :=
  ([Examples.SumTo.sumTo, Examples.Arith.gcd, Examples.Arith.popcount, Examples.Arith.sub32,
   Examples.Arith.sub32u, Examples.Arith.safeDivGt1, Examples.ArraySum.arraySum,
   Examples.Copy.copy, Examples.Hash.fnv1a, Examples.RingBuffer.rbPush, Examples.RingBuffer.rbPop,
   Examples.Search.findFirst, Examples.Search.lowerBound]
  ++ Tests.PrinterStress.all).map (·, [])
  ++ [(Examples.ParseU32.isDigit, Examples.ParseU32.prog),
      (Examples.ParseU32.parseU32, Examples.ParseU32.prog)]

/-- Every function, once (for `lc emit`). -/
def allFns : List Fn :=
  difftestFns.map (·.1)

#guard (cTranslationUnit allFns).isOk

end Tests
