import Proof.Privacy.Simulator.Arithmetic.EncLinkIndexCode
import Proof.Privacy.Simulator.Arithmetic.QueryInputProtocol
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every scheduled index fits the fixed fourteen-bit reader. -/
theorem encLinkIndexValue_bound (index : EncPRF.PermutationIndex) : encLinkIndexValue index < 2 ^ 14 := by
  have bound := (Fintype.equivFin EncPRF.PermutationIndex index).isLt
  have small : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
    simpa only [encPermutationIndex_count] using bound
  unfold encLinkIndexValue
  omega

/-- The schedule has exactly 508 labels. -/
theorem encLinkIndices_length : encLinkIndices.length = 508 := by
  simp [encLinkIndices, coordinateBitCount]

/-- The fixed prelude has exactly 7112 charged pushes. -/
theorem encLinkIndexPrelude_length : encLinkIndexPrelude.length = 7112 := by
  have lengths : ∀ index, (encLinkIndexBits index).length = 14 := by intro index; simp [encLinkIndexBits]
  have wire : encLinkIndexWire.length = encLinkIndices.length * 14 := by
    unfold encLinkIndexWire
    induction encLinkIndices with
    | nil => simp
    | cons head tail ih => simp [lengths, ih, Nat.add_mul, Nat.add_comm]
  simpa [encLinkIndexPrelude, encLinkIndices_length] using wire

/-- A fixed push list changes only the selected bit stack. -/
theorem executeLinear_pushList (stack : Fin 4) (source : List Bool) (memory : Memory) :
    executeLinear (source.map (LinearInstruction.push stack)) memory =
      { memory with bits := Function.update memory.bits stack (source.reverse ++ memory.bits stack) } := by
  induction source generalizing memory with
  | nil => simp [executeLinear]
  | cons bit source ih =>
      change executeLinear (source.map (LinearInstruction.push stack))
        ((LinearInstruction.push stack bit).execute memory) = _
      rw [ih]
      simp [LinearInstruction.execute, List.reverse_cons, List.append_assoc]

/-- The fixed prelude retains the caller suffix and all permanent data. -/
theorem encLinkIndexPrelude_memory (memory : Memory) :
    executeLinear encLinkIndexPrelude memory =
      { memory with bits := Function.update memory.bits 0 (encLinkIndexWire ++ memory.bits 0) } := by
  rw [encLinkIndexPrelude, executeLinear_pushList]
  simp

end Kriterion.ArgoMAC.ArithmeticSimulator
