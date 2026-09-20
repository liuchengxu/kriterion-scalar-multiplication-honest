import Proof.Privacy.Simulator.Arithmetic.PublicHistory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The history machine contains the forward setup. -/
theorem publicHistory_forward : ContainsLinear publicHistory publicHistoryForward publicHistoryForwardLabels := by
  intro index valid
  have bound : index < 6 := valid
  simp [publicHistory, publicHistoryForwardLabels, publicHistoryLabels, bound,
    show 7 ≤ 7 + index by omega, show 7 + index < 13 by omega]

/-- The history machine contains the inverse setup. -/
theorem publicHistory_inverse : ContainsLinear publicHistory publicHistoryInverse publicHistoryInverseLabels := by
  intro index valid
  have bound : index < 4 := valid
  simp [publicHistory, publicHistoryInverseLabels, publicHistoryLabels, bound,
    show ¬ (7 ≤ 13 + index ∧ 13 + index < 13) by omega,
    show 13 ≤ 13 + index by omega, show 13 + index < 17 by omega]

/-- The history machine contains the complete append block. -/
theorem publicHistory_append : ContainsLinear publicHistory historyAppend publicHistoryAppendLabels := by
  intro index valid
  have bound : index < 15 := valid
  simp [publicHistory, publicHistoryAppendLabels, publicHistoryLabels, bound,
    show ¬ (7 ≤ 17 + index ∧ 17 + index < 13) by omega,
    show ¬ (13 ≤ 17 + index ∧ 17 + index < 17) by omega,
    show 17 ≤ 17 + index by omega, show 17 + index < 32 by omega]

/-- The history machine restores the reply before its return. -/
theorem publicHistory_restore : ContainsLinear publicHistory publicHistoryRestore publicHistoryRestoreLabels := by
  intro index valid
  have bound : index < 2 := valid
  simp [publicHistory, publicHistoryRestoreLabels, publicHistoryLabels, bound,
    show ¬ (7 ≤ 32 + index ∧ 32 + index < 13) by omega,
    show ¬ (13 ≤ 32 + index ∧ 32 + index < 17) by omega,
    show ¬ (17 ≤ 32 + index ∧ 32 + index < 32) by omega,
    show 32 ≤ 32 + index by omega, show 32 + index < 34 by omega]

/-- The caller supplies the final return instruction. -/
def ContainsPublicHistory (host : Machine) (labels : Fin 35 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 35, pc.val < 34 → host.code[(labels pc).val] =
    relocate labels (publicHistory.code[pc.val]'pc.isLt)

end Kriterion.ArgoMAC.ArithmeticSimulator
