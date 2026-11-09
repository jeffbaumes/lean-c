import Lean

/-! The `lc_simp` simp set used by `lc_auto`. Tag your own spec lemmas with
`attribute [lc_simp] foo` (or pass them to `lc_auto [foo]`). -/

register_simp_attr lc_simp
