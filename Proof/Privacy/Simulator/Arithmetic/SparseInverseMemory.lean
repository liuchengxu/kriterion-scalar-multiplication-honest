import Proof.Privacy.Simulator.Arithmetic.SparseInverseFresh
import Proof.Privacy.Simulator.Arithmetic.StoredInverseSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The exchanged-table query stores the exact inverse source state on every path. -/
theorem permutationInverseSamples_memory [BN254.FieldCertificate] {size : Nat}
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation size) (input : Fin size)
    (represented : SparseTableData memory.ram oracle state) (sizeFits : size < 2 ^ 256)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (domain : memory.registers 5 = BitVec.ofNat 256 size)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (inputBase : memory.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 state.used)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 state.used)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts state.used state.used memory).support) :
    SparseMemory (inverseCommitted final).ram oracle (sparseInverseMemoryState state input final) := by
  have source := knownQueryScan_finite state.reverse input memory sizeFits used operand
    (by simpa only [SparsePermutation.reverse, represented.outputLength] using inputCounter)
    (by simpa only [SparsePermutation.reverse, represented.inputLength] using outputCounter)
    (by simpa only [SparsePermutation.reverse, inputBase] using represented.outputs)
    (by simpa only [SparsePermutation.reverse, outputBase] using represented.inputs)
  rw [show state.reverse.inputs.length = state.used from represented.outputLength,
    show state.reverse.outputs.length = state.used from represented.inputLength] at source
  by_cases known : (state.reverse.input.symm input).val < state.reverse.used
  · rw [if_pos known] at source
    have flag := congrArg Prod.snd source
    change (knownQueryScan state.used state.used memory).1.registers 7 = 1#256 at flag
    have nonzero : (knownQueryScan state.used state.used memory).1.registers 7 ≠ 0#256 := by
      rw [flag]
      decide
    unfold permutationForwardSamples at supported
    simp only [if_neg nonzero, PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    rw [sparseInverseMemoryState, sparseForwardMemoryState_known state.reverse input _ known,
      SparsePermutation.reverse_reverse, inverseCommitted_ram]
    exact knownQuery_committed_sparse state.used memory oracle state represented used header (by omega)
  · rw [if_neg known] at source
    have position := congrArg Prod.fst source
    have flag := congrArg Prod.snd source
    change (knownQueryScan state.used state.used memory).1.registers 7 = 0#256 at flag
    unfold permutationForwardSamples at supported
    simp only [if_pos flag] at supported
    obtain ⟨⟨sampled, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    have data := (knownQueryScan_data state.used state.used memory).1
    exact freshQuery_sample_inverseMemoryState attempts (knownQueryScan state.used state.used memory).1 sampled spent member
      oracle state input (by simpa only [data] using represented) known sizeFits
      ((knownQueryScan_metadata _ _ _ 0 (by decide)).trans used)
      ((knownQueryScan_metadata _ _ _ 5 (by decide)).trans domain)
      ((knownQueryScan_metadata _ _ _ 1 (by decide)).trans inputBase)
      ((knownQueryScan_metadata _ _ _ 3 (by decide)).trans outputBase)
      position ((congrFun data 13).trans header) fits

/-- The inverse commit preserves the state recovered from its reply. -/
theorem inverseCommitted_memoryState {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) :
    sparseInverseMemoryState state input (inverseCommitted memory) = sparseInverseMemoryState state input memory := by
  simp only [sparseInverseMemoryState, sparseForwardMemoryState, inverseCommitted_queryValue]

/-- The loaded inverse handler preserves the complete finite RAM relation. -/
theorem storedInverseSamples_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts state.used memory).support) :
    SparseMemory final.ram oracle (sparseInverseMemoryState state input final) := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [inverseCommitted_memoryState]
  have metadata := inverseLoaded_metadata memory
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented (by omega)
  apply permutationInverseSamples_memory attempts (inverseLoaded memory) before spent oracle state input
    (by simpa only [metadata.1] using loaded.toSparseTableData) (by decide) (metadata.2.1.trans used)
  · rw [metadata.2.2.2.2.2.2.1]
    simp [oracleLoaded]
  · exact metadata.2.2.2.2.2.2.2.trans ((oracleLoaded_query memory).1.trans operand)
  · rw [metadata.2.2.1]
    exact oracleLoaded_outputBase memory oracle state.used index represented.count (by omega)
  · rw [metadata.2.2.2.1]
    exact oracleLoaded_inputBase memory oracle state.used index represented.count (by omega)
  · rw [metadata.2.2.2.2.1]
    simpa [oracleLoaded] using used
  · rw [metadata.2.2.2.2.2.1]
    simpa [oracleLoaded] using used
  · rw [metadata.1]
    exact (oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address])
  · exact fits
  · exact member

/-- The inverse RAM relation keeps the old state after failure and the exact new state after success. -/
theorem storedInverseSamples_joint_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts state.used memory).support) :
    match queryValue final with
    | none => SparseMemory final.ram oracle state
    | some word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        SparseMemory final.ram oracle (sparseForwardNext state.reverse input value).reverse := by
  have stored := storedInverseSamples_memory attempts memory final cost oracle state input represented index operand fits supported
  unfold sparseInverseMemoryState sparseForwardMemoryState at stored
  cases observed : queryValue final <;>
    simpa only [observed, Option.map_none, Option.map_some, Option.getD_none, Option.getD_some,
      SparsePermutation.reverse_reverse] using stored

end Kriterion.ArgoMAC.ArithmeticSimulator
