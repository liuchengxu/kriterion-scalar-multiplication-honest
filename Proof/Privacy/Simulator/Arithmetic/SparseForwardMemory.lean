import Proof.Privacy.Simulator.Arithmetic.SparseFreshMemory
import Proof.Privacy.Simulator.Arithmetic.StoredForward

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Every supported forward result stores its recovered finite state after the count commit. -/
theorem permutationForwardSamples_memory [BN254.FieldCertificate] {size : Nat}
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation size) (input : Fin size)
    (represented : SparseTableData memory.ram oracle state) (sizeFits : size < 2 ^ 256)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (domain : memory.registers 5 = BitVec.ofNat 256 size)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 state.used)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 state.used)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (permutationForwardSamples attempts state.used state.used memory).support) :
    SparseMemory (oracleCommitted final).ram oracle (sparseForwardMemoryState state input final) := by
  have source := knownQueryScan_finite state input memory sizeFits used operand
    (by simpa only [represented.inputLength] using inputCounter)
    (by simpa only [represented.outputLength] using outputCounter)
    (by simpa only [inputBase] using represented.inputs)
    (by simpa only [outputBase] using represented.outputs)
  rw [represented.inputLength, represented.outputLength] at source
  by_cases known : (state.input.symm input).val < state.used
  · rw [if_pos known] at source
    have flag := congrArg Prod.snd source
    change (knownQueryScan state.used state.used memory).1.registers 7 = 1#256 at flag
    have nonzero : (knownQueryScan state.used state.used memory).1.registers 7 ≠ 0#256 := by
      rw [flag]
      decide
    unfold permutationForwardSamples at supported
    simp only [if_neg nonzero, PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    rw [sparseForwardMemoryState_known state input _ known]
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
    exact freshQuery_sample_memoryState attempts (knownQueryScan state.used state.used memory).1 sampled spent member
      oracle state input (by simpa only [data] using represented) known sizeFits
      ((knownQueryScan_metadata _ _ _ 0 (by decide)).trans used)
      ((knownQueryScan_metadata _ _ _ 5 (by decide)).trans domain)
      ((knownQueryScan_metadata _ _ _ 1 (by decide)).trans inputBase)
      ((knownQueryScan_metadata _ _ _ 3 (by decide)).trans outputBase)
      position ((congrFun data 13).trans header) fits

/-- The count commit leaves the accepted answer and cutoff flag unchanged. -/
theorem oracleCommitted_queryValue (memory : Memory) :
    queryValue (oracleCommitted memory) = queryValue memory := by
  simp [queryValue, oracleCommitted]

/-- The count commit preserves the recovered finite state. -/
theorem oracleCommitted_memoryState {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) :
    sparseForwardMemoryState state input (oracleCommitted memory) = sparseForwardMemoryState state input memory := by
  simp only [sparseForwardMemoryState, oracleCommitted_queryValue]

/-- The loaded forward handler preserves the full finite source RAM relation on every path. -/
theorem storedForwardSamples_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.used memory).support) :
    SparseMemory final.ram oracle (sparseForwardMemoryState state input final) := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [oracleCommitted_memoryState]
  have used := (oracleLoaded_used memory oracle index).trans represented.count
  have loaded := SparseMemory.loaded memory oracle state represented (by omega)
  apply permutationForwardSamples_memory attempts (oracleLoaded memory) before spent oracle state input
    loaded.toSparseTableData (by decide) used
  · simp [oracleLoaded]
  · exact (oracleLoaded_query memory).1.trans operand
  · exact oracleLoaded_inputBase memory oracle state.used index represented.count (by omega)
  · exact oracleLoaded_outputBase memory oracle state.used index represented.count (by omega)
  · simpa [oracleLoaded] using used
  · simpa [oracleLoaded] using used
  · exact (oracleLoaded_query memory).2.2.2.trans (by rw [index, oracleHeader_address])
  · exact fits
  · exact member

end Kriterion.ArgoMAC.ArithmeticSimulator
