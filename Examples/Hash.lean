import LC

/-!
# FNV-1a (32-bit) over a byte buffer

A real hash with a wrapping multiply. It's tested (known-answer test here, differential
testing in `lake exe lc difftest`) but not yet proved against a reference.
-/

open LC

namespace Examples.Hash

/-- FNV-1a, 32-bit, over a byte buffer: a real function with wrapping multiply. -/
def fnv1a : Fn where
  name   := "fnv1a"
  params := [("p", .ptr .u8), ("n", .int .u32)]
  locals := [("i", .int .u32), ("c", .int .u8), ("h", .int .u32)]
  body   := .block [
    "h" ::= .u32 2166136261,
    "i" ::= .u32 0,
    .while (v "i" <. v "n") (.block [
      .load "c" (v "p") (v "i"),
      "h" ::= (v "h" ^^^ .cast .u32 (v "c")) * .u32 16777619,
      "i" ::= v "i" + .u32 1
    ])
  ]
  ret    := .int .u32
  result := v "h"

-- Known-answer test: FNV-1a("a") = 0xe40c292c.
#guard fnv1a.callMem [.ptr .u8 ⟨0, 0⟩, .u32 1] [(0, [.u8 97])] = .ok (.u32 0xe40c292c, [(0, [.u8 97])])


end Examples.Hash
