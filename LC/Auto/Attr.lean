import Lean

/-! The `lc_simp` simp set used by `lc_auto`. Tag your own spec lemmas with
`attribute [lc_simp] foo` (or pass them to `lc_auto [foo]`). -/

register_simp_attr lc_simp

register_option lc_auto.heartbeats : Nat := {
  defValue := 100000
  descr := "lc_auto: heartbeat budget (in thousands, like maxHeartbeats) for evaluating one \
    expression or closing one leaf goal. A leaf over budget is left open with a warning; an \
    expression over budget is an error. 0 means no budget beyond maxHeartbeats."
}
