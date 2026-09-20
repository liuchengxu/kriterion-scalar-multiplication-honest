import Proof.Privacy.Simulator.Arithmetic.SparseForwardJoint
import Proof.Privacy.Simulator.Arithmetic.FreshQueryMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The known-query scan implements the finite source position test. -/
theorem knownQueryScan_finite [BN254.FieldCertificate] {size : Nat}
    (state : SparsePermutation size) (input : Fin size) (memory : Memory)
    (sizeFits : size < 2 ^ 256)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 state.inputs.length)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 state.outputs.length)
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) (sparseWordPairs state.inputs))
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) (sparseWordPairs state.outputs)) :
    ((knownQueryScan state.inputs.length state.outputs.length memory).1.registers 8,
      (knownQueryScan state.inputs.length state.outputs.length memory).1.registers 7) =
      if (state.input.symm input).val < state.used then
        (BitVec.ofNat 256 (state.output (state.input.symm input)).val, 1#256)
      else (BitVec.ofNat 256 (state.input.symm input).val, 0#256) := by
  have inputLength : (sparseWordPairs state.inputs).length = state.inputs.length := by simp [sparseWordPairs]
  have outputLength : (sparseWordPairs state.outputs).length = state.outputs.length := by simp [sparseWordPairs]
  have source := knownQueryScan_source (sparseWordPairs state.inputs) (sparseWordPairs state.outputs) memory
    (by rw [inputLength]; exact lt_of_le_of_lt (state.inputLength.trans state.within) sizeFits)
    (by rw [outputLength]; exact lt_of_le_of_lt (state.outputLength.trans state.within) sizeFits)
    (by simpa only [inputLength] using inputCounter) (by simpa only [outputLength] using outputCounter)
    inputStored outputStored
  simp only [inputLength, outputLength] at source
  have position : (swaps (sparseWordPairs state.inputs)).symm (memory.registers 8) =
      BitVec.ofNat 256 (state.input.symm input).val := by
    rw [operand]
    exact encoded_swaps_inverse state.inputs input (Nat.le_of_lt sizeFits)
  rw [position, used] at source
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_of_le_of_lt state.within sizeFits),
    Nat.mod_eq_of_lt (lt_trans (state.input.symm input).isLt sizeFits)] at source
  rw [source]
  split
  next known =>
    exact Prod.ext (encoded_swaps _ (finiteWord_injective size (Nat.le_of_lt sizeFits)) state.outputs (state.input.symm input)) rfl
  next fresh => rfl

/-- A failed query retains the old state in the RAM relation. -/
def sparseForwardMemoryState {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) : SparsePermutation size :=
  ((queryValue memory).map fun word =>
    sparseForwardNext state input (sparseWordValue size (by have := input.isLt; omega) word)).getD state

/-- A known input preserves the old state for every observed memory result. -/
theorem sparseForwardMemoryState_known {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) (known : (state.input.symm input).val < state.used) :
    sparseForwardMemoryState state input memory = state := by
  unfold sparseForwardMemoryState
  cases queryValue memory <;> simp [sparseForwardNext, known]

/-- A failed result explicitly retains the old sparse state. -/
theorem sparseForwardMemoryState_failed {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) (failed : memory.registers 7 = 0#256) :
    sparseForwardMemoryState state input memory = state := by
  simp [sparseForwardMemoryState, queryValue, failed]

/-- An accepted source reply recovers its exact extension coordinates. -/
theorem sparseForwardMemoryState_fresh {size : Nat} (state : SparsePermutation size) (input chosen : Fin size)
    (memory : Memory) (fresh : ¬ (state.input.symm input).val < state.used) (sizeFits : size ≤ 2 ^ 256)
    (value : queryValue memory = some (BitVec.ofNat 256 (state.output chosen).val)) :
    sparseForwardMemoryState state input memory =
      state.extend (by have := (state.input.symm input).isLt; omega) (state.input.symm input) chosen := by
  simp [sparseForwardMemoryState, value, sparseWordValue_encoded _ _ sizeFits,
    sparseForwardNext, fresh]

end Kriterion.ArgoMAC.ArithmeticSimulator
