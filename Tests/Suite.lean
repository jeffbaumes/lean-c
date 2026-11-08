import Examples
import Tests.PrinterStress

/-!
# The differential-test suite

Every function `lake exe lc difftest` runs against the interpreter.
-/

open LC

namespace Tests

def difftestFns : List Fn :=
  [Examples.SumTo.sumTo, Examples.Arith.gcd, Examples.Arith.popcount, Examples.Arith.sub32,
   Examples.Arith.sub32u, Examples.Arith.safeDivGt1, Examples.ArraySum.arraySum,
   Examples.Copy.copy, Examples.Hash.fnv1a, Examples.RingBuffer.rbPush, Examples.RingBuffer.rbPop]
  ++ Tests.PrinterStress.all

#guard (cTranslationUnit difftestFns).isOk

end Tests
