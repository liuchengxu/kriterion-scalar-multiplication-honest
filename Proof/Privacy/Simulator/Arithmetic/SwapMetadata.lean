import Construction.Simulator.SwapMetadata
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Proof.Privacy.Simulator.OperationalOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The seven fixed instructions exchange the metadata exactly. -/
theorem swapMetadata_memory (memory : Memory) :
    executeLinear swapMetadata memory = metadataSwapped memory := by
  simp [executeLinear, swapMetadata, LinearInstruction.execute, Arithmetic.eval,
    metadataSwapped, Function.update_comm]

/-- The metadata exchange preserves the query result and all stored state. -/
theorem metadataSwapped_frame (memory : Memory) :
    (metadataSwapped memory).registers 0 = memory.registers 0 ∧
    (metadataSwapped memory).registers 5 = memory.registers 5 ∧
    (metadataSwapped memory).registers 7 = memory.registers 7 ∧
    (metadataSwapped memory).registers 8 = memory.registers 8 ∧
    (metadataSwapped memory).bits = memory.bits ∧ (metadataSwapped memory).ram = memory.ram := by
  simp [metadataSwapped]

/-- The metadata exchange returns after seven charged instructions. -/
theorem swapMetadata_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host swapMetadata labels)
    (memory : Memory) (fuel : Nat) :
    run host (7 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 7, metadataSwapped memory⟩).map
        (Option.map fun result => (result.1, result.2 + 7)) := by
  have length : swapMetadata.length = 7 := rfl
  simpa only [swapMetadata_memory, length] using linear_continue host swapMetadata labels present memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.Security.OperationalOracle

/-- The dual state exchanges the sparse permutation's input and output tables. -/
def SparsePermutation.dual {size : Nat} (state : SparsePermutation size) : SparsePermutation size :=
  ⟨state.used, state.within, state.outputs, state.inputs, state.outputLength, state.inputLength⟩

/-- Exchanging both tables twice restores the original sparse state. -/
theorem SparsePermutation.dual_dual {size : Nat} (state : SparsePermutation size) :
    state.dual.dual = state := by cases state; rfl

/-- A fresh dual update exchanges the two transpositions. -/
theorem SparsePermutation.dual_extend {size : Nat} (state : SparsePermutation size)
    (room : state.used < size) (input output : Fin size) :
    (state.dual.extend room input output).dual = state.extend room output input := by
  cases state
  rfl

/-- One forward query on the dual state gives exactly one inverse query. -/
theorem SparsePermutation.dual_forward {size : Nat} (state : SparsePermutation size) (value : Fin size) :
    (state.dual.forward value).map (fun result => (result.1, result.2.dual)) = state.inverse value := by
  unfold forward inverse
  simp only [dual, input, output]
  by_cases known : ((swaps state.outputs).symm value).val < state.used
  · simp [known, Draw.map, dual_dual]
  · simp [known, Draw.map, dual, extend, suffix, Function.comp_def]

end Kriterion.ArgoMAC.Security.OperationalOracle
