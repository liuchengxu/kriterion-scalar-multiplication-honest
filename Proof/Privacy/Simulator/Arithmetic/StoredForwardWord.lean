import Proof.Privacy.Simulator.Arithmetic.StoredForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The loaded forward handler has the complete operational cutoff law. -/
theorem storedForwardSamples_wordReply [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.used ≤ 2 ^ 110) :
    (storedForwardSamples attempts state.used memory).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented fits
  have inputBase := oracleLoaded_inputBase memory oracle state.used index represented.count fits
  have outputBase := oracleLoaded_outputBase memory oracle state.used index represented.count fits
  have source := permutationForwardSamples_finite attempts state input (oracleLoaded memory) (by decide) used
    (by simp [oracleLoaded]) ((oracleLoaded_query memory).1.trans operand)
    (by simpa [oracleLoaded, loaded.inputLength] using used)
    (by simpa [oracleLoaded, loaded.outputLength] using used)
    (by simpa only [inputBase] using loaded.inputs)
    (by simpa only [outputBase] using loaded.outputs)
    (by
      intro offset inside
      rw [outputBase]
      exact descendingPairs_safe oracle 1 state.used offset fits (by simpa only [loaded.outputLength] using inside))
  rw [loaded.inputLength, loaded.outputLength] at source
  simpa only [storedForwardSamples, PMF.map_comp, Function.comp_def, oracleCommitted_queryValue] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
