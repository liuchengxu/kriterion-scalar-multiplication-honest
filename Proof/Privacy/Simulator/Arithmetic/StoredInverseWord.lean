import Proof.Privacy.Simulator.Arithmetic.StoredInverseSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The loaded inverse handler has the complete operational cutoff law. -/
theorem storedInverseSamples_wordReply [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.used ≤ 2 ^ 110) :
    (storedInverseSamples attempts state.used memory).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.inverse input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  have metadata := inverseLoaded_metadata memory
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented fits
  have inputBase := oracleLoaded_inputBase memory oracle state.used index represented.count fits
  have outputBase := oracleLoaded_outputBase memory oracle state.used index represented.count fits
  have source := permutationForwardSamples_finite attempts state.reverse input (inverseLoaded memory) (by decide)
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
  rw [SparsePermutation.inverse_reverse_forward, drawCutoffLaw_map, PMF.map_comp]
  simpa only [storedInverseSamples, PMF.map_comp, Function.comp_def, Option.map_map,
    inverseCommitted_queryValue] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
