import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNull

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine

/-- The selector store sequence preserves every bit stack. -/
theorem selectedLabelStores_bits (indices : List (Fin 508)) (memory : Memory) :
    (executeLinear (selectedLabelStores indices) memory).bits = memory.bits := by
  induction indices generalizing memory with
  | nil => rfl
  | cons index rest ih =>
      simp only [selectedLabelStores, List.flatMap_cons, executeLinear_append]
      exact (ih _).trans (selectedLabelStore_bits index memory)

/-- The full original-label store preserves every bit stack. -/
theorem selectedLabelStoreCode_bits (memory : Memory) :
    (executeLinear selectedLabelStoreCode memory).bits = memory.bits := by
  rw [selectedLabelStoreCode_eq, selectedLabelStoreProgram]
  exact selectedLabelStores_bits _ memory

/-- The complete curve arithmetic preserves every bit stack. -/
theorem retargetCurveCode_bits (memory : Memory) :
    (executeLinear retargetCurveCode memory).bits = memory.bits := by
  rw [retargetCurveCode_eq, retargetCurveProgram, executeLinear_append]
  exact (retargetAt_preserves .curve 834395 11 0 _ (by decide) (by decide)).1.trans
    (retargetInput_preserves memory).2.1

/-- The online reader changes only the input bit stack. -/
theorem onlineInputMemory_bits [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    (onlineInputMemory memory input output rest).bits = Function.update memory.bits 0 rest := by
  cases output with
  | none =>
      simp [onlineInputMemory, onlineNullMemory, onlineInputZero, onlineBranchMemory, onlineTaggedMemory,
        onlineReadStored, onlineStored, decodedInput, inputFinal, inputFrame, executeLinear, LinearInstruction.execute]
  | some output =>
      cases output <;>
        simp [onlineInputMemory, onlineNullMemory, onlineAffineMemory, onlineInputZero, onlineBranchMemory,
          onlineTaggedMemory, onlineReadStored, onlineStored, decodedInput, inputFinal, inputFrame,
          executeLinear, LinearInstruction.execute]

/-- The complete common prefix retains the unread suffix and every other bit stack. -/
theorem onlineCurveMemory_bits [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    (onlineCurveMemory memory input output rest).bits = Function.update memory.bits 0 rest := by
  rw [onlineCurveMemory, retargetCurveCode_bits, onlineOriginalMemory, selectedLabelStoreCode_bits,
    (onlineOriginalSetup_state _).2.1, onlineReadMemory, onlineInputMemory_bits]
  rfl

/-- The absent-output gate setup preserves the common prefix's bit stacks. -/
theorem onlineNullGateInitial_bits (memory : Memory) : (onlineNullGateInitial memory).bits = memory.bits :=
  (onlineOriginalSetup_state (onlineTagMemory memory)).2.1

end Kriterion.ArgoMAC.ArithmeticSimulator
