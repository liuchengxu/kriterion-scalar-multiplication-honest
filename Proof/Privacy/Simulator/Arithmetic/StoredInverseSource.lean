import Proof.Privacy.Simulator.Arithmetic.StoredForwardSource
import Proof.Privacy.Simulator.Arithmetic.StoredInverse

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The inverse commit preserves the reply and cutoff flag. -/
theorem inverseCommitted_queryValue (memory : Memory) :
    queryValue (inverseCommitted memory) = queryValue memory := by
  simp [inverseCommitted, queryValue, oracleCommitted, metadataSwapped]

/-- The inverse metadata keeps the loaded state and exchanges both table addresses. -/
theorem inverseLoaded_metadata (memory : Memory) :
    (inverseLoaded memory).ram = (oracleLoaded memory).ram ∧
    (inverseLoaded memory).registers 0 = (oracleLoaded memory).registers 0 ∧
    (inverseLoaded memory).registers 1 = (oracleLoaded memory).registers 3 ∧
    (inverseLoaded memory).registers 3 = (oracleLoaded memory).registers 1 ∧
    (inverseLoaded memory).registers 2 = (oracleLoaded memory).registers 4 ∧
    (inverseLoaded memory).registers 4 = (oracleLoaded memory).registers 2 ∧
    (inverseLoaded memory).registers 5 = (oracleLoaded memory).registers 5 ∧
    (inverseLoaded memory).registers 8 = (oracleLoaded memory).registers 8 := by
  simp [inverseLoaded, metadataSwapped]

/-- The loaded inverse handler has the complete operational cutoff law. -/
theorem storedInverseSamples_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.used ≤ 2 ^ 110) :
    (storedInverseSamples attempts state.used memory).map
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, (sparseForwardNext state.reverse input value).reverse)) =
      drawCutoffLaw attempts (state.inverse input) := by
  have metadata := inverseLoaded_metadata memory
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented fits
  have inputBase := oracleLoaded_inputBase memory oracle state.used index represented.count fits
  have outputBase := oracleLoaded_outputBase memory oracle state.used index represented.count fits
  have source := permutationForwardSamples_joint attempts state.reverse input (inverseLoaded memory) (by decide)
    (metadata.2.1.trans used)
    (by rw [metadata.2.2.2.2.2.2.1]; simp [oracleLoaded])
    (metadata.2.2.2.2.2.2.2.trans ((oracleLoaded_query memory).1.trans operand))
    (by rw [metadata.2.2.2.2.1]; simpa [SparsePermutation.reverse, oracleLoaded, loaded.outputLength] using used)
    (by rw [metadata.2.2.2.2.2.1]; simpa [SparsePermutation.reverse, oracleLoaded, loaded.inputLength] using used)
    (by rw [metadata.1, metadata.2.2.1, outputBase]; exact loaded.outputs)
    (by rw [metadata.1, metadata.2.2.2.1, inputBase]; exact loaded.inputs)
    (by
      intro offset inside
      rw [metadata.2.2.2.1, inputBase]
      exact descendingPairs_safe oracle 0 state.used offset fits
        (by simpa only [SparsePermutation.reverse, loaded.inputLength] using inside))
  rw [show state.reverse.inputs.length = state.used from loaded.outputLength,
    show state.reverse.outputs.length = state.used from loaded.inputLength] at source
  have joint := congrArg (PMF.map (Option.map fun result : Fin (2 ^ 128) × SparsePermutation (2 ^ 128) =>
    (result.1, result.2.reverse))) source
  rw [← drawCutoffLaw_map, ← SparsePermutation.inverse_reverse_forward] at joint
  simpa only [storedInverseSamples, PMF.map_comp, Function.comp_def, Option.map_map,
    inverseCommitted_queryValue] using joint

end Kriterion.ArgoMAC.ArithmeticSimulator
