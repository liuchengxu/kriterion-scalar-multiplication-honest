import Proof.Privacy.Simulator.Arithmetic.SparseForwardMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The loaded forward handler has the complete operational cutoff law. -/
theorem storedForwardSamples_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.used ≤ 2 ^ 110) :
    (storedForwardSamples attempts state.used memory).map
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, sparseForwardNext state input value)) =
      drawCutoffLaw attempts (state.forward input) := by
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented fits
  have inputBase := oracleLoaded_inputBase memory oracle state.used index represented.count fits
  have outputBase := oracleLoaded_outputBase memory oracle state.used index represented.count fits
  have source := permutationForwardSamples_joint attempts state input (oracleLoaded memory) (by decide) used
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

/-- The joint source and the RAM relation use the same accepted state. -/
theorem storedForwardSamples_joint_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.used memory).support) :
    match queryValue final with
    | none => SparseMemory final.ram oracle state
    | some word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        SparseMemory final.ram oracle (sparseForwardNext state input value) := by
  have stored := storedForwardSamples_memory attempts memory final cost oracle state input represented index operand fits supported
  unfold sparseForwardMemoryState at stored
  cases observed : queryValue final <;> simpa only [observed, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some] using stored

end Kriterion.ArgoMAC.ArithmeticSimulator
