import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The controller compares the remaining label count with the coordinate boundary. -/
def encLinkCompared (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 3 (memory.registers 2 ^^^ 254#256) }

/-- The controller chooses the next iteration or the final return. -/
def encLinkControlState (memory : Memory) : Memory × Nat × Fin 7468 :=
  if memory.registers 2 = 0#256 then (executeLinear encLinkReturn memory, 3, 7466)
  else if memory.registers 2 = 254#256 then
    (executeLinear encLinkSwitch (encLinkCompared memory), 8, 7208)
  else (encLinkCompared memory, 4, 7208)

/-- The final count test restores the output pointer before the host return. -/
theorem encLinkBlock_done [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (done : memory.registers 2 = 0#256) :
    runPrefix host 3 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false, ⟨labels 7466, executeLinear encLinkReturn memory⟩, 3)) := by
  have gate : host.code[(labels 7456).val] = .branch 2 (labels 7464) (labels 7457) := by
    exact (present 7456 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).1)
  have block := encLinkBlock_linear host attempts labels present encLinkReturn encLinkReturnLabels
    (encLink_result attempts) (by
      intro index valid
      have bound : index < 2 := valid
      simp [encLinkReturnLabels, encLinkLabels, bound]
      omega)
  have returned := linear_prefix host encLinkReturn (labels ∘ encLinkReturnLabels) block memory
  change runPrefix host 2 ⟨labels 7464, memory⟩ = _ at returned
  rw [show 3 = 2 + 1 from rfl, runPrefix]
  simp only [step, gate, show (0 : Word) = 0#256 from rfl, done, ↓reduceIte, PMF.pure_bind]
  rw [returned]
  simp [PMF.pure_map, encLinkReturnLabels, encLinkLabels, show encLinkReturn.length = 2 from rfl]

/-- The nonfinal controller consumes four instructions before its next block. -/
theorem encLinkBlock_compare [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (more : memory.registers 2 ≠ 0#256) :
    runPrefix host 4 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false,
        ⟨if memory.registers 2 = 254#256 then labels 7460 else labels 7208,
          encLinkCompared memory⟩, 4)) := by
  have gate : host.code[(labels 7456).val] = .branch 2 (labels 7464) (labels 7457) := by
    exact (present 7456 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).1)
  have constant : host.code[(labels 7457).val] = .constant 3 254 (labels 7458) := by
    exact (present 7457 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.1)
  have compare : host.code[(labels 7458).val] = .arithmetic .xor 3 2 3 (labels 7459) := by
    exact (present 7458 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.2.1)
  have select : host.code[(labels 7459).val] = .branch 3 (labels 7460) (labels 7208) := by
    exact (present 7459 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.2.2)
  simp [runPrefix, step, gate, constant, compare, select, more, encLinkCompared,
    Arithmetic.eval, PMF.pure_map, BitVec.xor_eq_zero_iff, show (0 : Word) = 0#256 from rfl]

/-- The controller returns the exact next state and instruction charge. -/
theorem encLinkBlock_control [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) :
    runPrefix host (encLinkControlState memory).2.1 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false,
        ⟨labels (encLinkControlState memory).2.2, (encLinkControlState memory).1⟩,
          (encLinkControlState memory).2.1)) := by
  by_cases done : memory.registers 2 = 0#256
  · simpa [encLinkControlState, done] using encLinkBlock_done host attempts labels present memory done
  · have compared := encLinkBlock_compare host attempts labels present memory done
    by_cases boundary : memory.registers 2 = 254#256
    · simp only [if_pos boundary] at compared
      have block := encLinkBlock_linear host attempts labels present encLinkSwitch encLinkSwitchLabels
        (encLink_switch attempts) (by
          intro index valid
          have bound : index < 4 := valid
          simp [encLinkSwitchLabels, encLinkLabels, bound]
          omega)
      have switched := linear_prefix host encLinkSwitch (labels ∘ encLinkSwitchLabels) block
        (encLinkCompared memory)
      change runPrefix host 4 ⟨labels 7460, encLinkCompared memory⟩ = _ at switched
      simp only [encLinkControlState, if_neg done, if_pos boundary]
      rw [show 8 = 4 + 4 from rfl, prefix_add, compared, PMF.pure_bind]
      dsimp only
      rw [switched]
      simp [PMF.pure_map, encLinkSwitchLabels, encLinkLabels,
        show encLinkSwitch.length = 4 from rfl]
    · simpa [encLinkControlState, done, boundary] using compared

end Kriterion.ArgoMAC.ArithmeticSimulator
