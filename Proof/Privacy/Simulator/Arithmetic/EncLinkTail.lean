import Proof.Privacy.Simulator.Arithmetic.EncLinkControl
import Proof.Privacy.Simulator.Arithmetic.InternalForwardReturn

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The query tail writes an accepted label or preserves the cutoff result. -/
def encLinkAfterQuery (memory : Memory) : Memory × Nat × Fin 7468 :=
  if memory.registers 7 = 0#256 then (memory, 0, 7467)
  else
    let controlled := encLinkControlState (executeLinear encLinkFinish memory)
    (controlled.1, 20 + controlled.2.1, controlled.2.2)

/-- The control path uses at most eight instructions. -/
theorem encLinkControlState_cost (memory : Memory) : (encLinkControlState memory).2.1 ≤ 8 := by
  unfold encLinkControlState
  split
  · change 3 ≤ 8; decide
  · split
    · change 8 ≤ 8; decide
    · change 4 ≤ 8; decide

/-- The accepted query tail writes one label and selects the exact next iteration. -/
theorem encLinkBlock_finishControl [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (fuel : Nat) :
    let controlled := encLinkControlState (executeLinear encLinkFinish memory)
    run host (28 + fuel) ⟨labels 7436, memory⟩ =
      (run host (28 + fuel - (20 + controlled.2.1))
        ⟨labels controlled.2.2, controlled.1⟩).map
          (Option.map fun result => (result.1, result.2 + (20 + controlled.2.1))) := by
  dsimp only
  have block := encLinkBlock_linear host attempts labels present encLinkFinish encLinkFinishLabels
    (encLink_finish attempts) (by
      intro index valid
      have bound : index < 20 := valid
      simp [encLinkFinishLabels, encLinkLabels, bound]
      omega)
  have finished := linear_continue host encLinkFinish (labels ∘ encLinkFinishLabels) block memory (8 + fuel)
  change run host (20 + (8 + fuel)) ⟨labels 7436, memory⟩ = _ at finished
  rw [show 28 + fuel = 20 + (8 + fuel) by omega, finished]
  change (run host (8 + fuel) ⟨labels 7456, executeLinear encLinkFinish memory⟩).map _ = _
  have bound := encLinkControlState_cost (executeLinear encLinkFinish memory)
  have enough : 8 + fuel = (encLinkControlState (executeLinear encLinkFinish memory)).2.1 +
      (8 + fuel - (encLinkControlState (executeLinear encLinkFinish memory)).2.1) := by omega
  conv_lhs => rw [enough, run_after_prefix,
    encLinkBlock_control host attempts labels present (executeLinear encLinkFinish memory), PMF.pure_bind]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  have rest : 20 + (8 + fuel) - (20 + (encLinkControlState (executeLinear encLinkFinish memory)).2.1) =
      8 + fuel - (encLinkControlState (executeLinear encLinkFinish memory)).2.1 := by omega
  rw [rest]
  simp [show encLinkFinish.length = 20 from rfl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The query tail preserves unused caller fuel on both success and cutoff failure. -/
theorem encLinkBlock_afterQuery [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (fuel : Nat) :
    run host (28 + fuel) ⟨labels (encLinkQueryLabels (internalForwardReturn memory)), memory⟩ =
      (run host (28 + fuel - (encLinkAfterQuery memory).2.1)
        ⟨labels (encLinkAfterQuery memory).2.2, (encLinkAfterQuery memory).1⟩).map
          (Option.map fun result => (result.1, result.2 + (encLinkAfterQuery memory).2.1)) := by
  by_cases rejected : memory.registers 7 = 0#256
  · simp [encLinkAfterQuery, internalForwardReturn, encLinkQueryLabels, rejected, PMF.map_id]
  · simpa [encLinkAfterQuery, internalForwardReturn, encLinkQueryLabels, rejected] using
      encLinkBlock_finishControl host attempts labels present memory fuel


end Kriterion.ArgoMAC.ArithmeticSimulator
