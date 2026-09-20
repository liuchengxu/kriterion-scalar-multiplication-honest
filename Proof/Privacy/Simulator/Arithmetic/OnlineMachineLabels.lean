import Proof.Privacy.Simulator.Arithmetic.OnlineMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each active block label uses its fixed instruction offset. -/
theorem onlineBodyLabels_active (start length : Nat) (inside : start + length ≤ 290305298)
    (normal : Fin 290305300) (index : Nat) (active : index < length) :
    (onlineBodyLabels start length inside normal index).val = start + index := by
  simp only [onlineBodyLabels, dif_pos active]

/-- Each sequential instruction returns to the next fixed instruction slot. -/
theorem onlineBodyLabels_next (start length : Nat) (inside : start + length ≤ 290305298)
    (index : Nat) (active : index < length) :
    onlineBodyLabels start length inside ⟨start + length, by omega⟩ (index + 1) =
      ⟨start + index + 1, by omega⟩ := by
  apply Fin.ext
  simp only [onlineBodyLabels]
  split <;> simp only <;> omega

/-- Each active branch block uses its fixed instruction offset. -/
theorem onlineBranchLabels_active (start length : Nat) (inside : start + length ≤ 290305298)
    (normal : Fin 290305300) (index : Nat) (active : index < length) :
    (onlineBranchLabels start length inside normal index).val = start + index := by
  simp only [onlineBranchLabels, dif_pos active]

end Kriterion.ArgoMAC.ArithmeticSimulator
