import Proof.Privacy.Simulator.Arithmetic.SparseQuerySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Every fresh path stores the source state recovered from its reply or its explicit failure. -/
theorem freshQuery_sample_memoryState [BN254.FieldCertificate] {size : Nat}
    (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size) (input : Fin size)
    (represented : SparseTableData original.ram oracle state)
    (fresh : ¬ (state.input.symm input).val < state.used) (sizeFits : size < 2 ^ 256)
    (used : original.registers 0 = BitVec.ofNat 256 state.used)
    (domain : original.registers 5 = BitVec.ofNat 256 size)
    (inputBase : original.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : original.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputValue : original.registers 8 = BitVec.ofNat 256 (state.input.symm input).val)
    (header : original.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (freshQueryTail state.used (freshChoiceFinal sampled)).1).ram oracle
      (sparseForwardMemoryState state input (freshQueryTail state.used (freshChoiceFinal sampled)).1) := by
  by_cases failed : (freshChoiceFinal sampled).registers 7 = 0#256
  · have tailFailed : (freshQueryTail state.used (freshChoiceFinal sampled)).1.registers 7 = 0#256 := by
      simp only [freshQueryTail, if_pos failed]
      exact failed
    rw [sparseForwardMemoryState_failed state input _ tailFailed]
    exact freshQuery_failed_sparse attempts original sampled cost supported oracle state represented
      used header failed (by omega)
  · have room : state.used < size := by have := (state.input.symm input).isLt; omega
    have reached : some ((freshChoiceFinal sampled).registers 9) ∈
        ((freshChoiceSamples attempts original).map
          (fun result => freshChoiceValue (freshChoiceFinal result.1))).support := by
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨(sampled, cost), supported, by simp [freshChoiceValue, failed]⟩
    have bound := freshChoice_chosen_bounds attempts size state.used original
      ((freshChoiceFinal sampled).registers 9) room (Nat.le_of_lt sizeFits) domain used reached
    let chosen : Fin size := ⟨((freshChoiceFinal sampled).registers 9).toNat, bound.2⟩
    have chosenWord : (freshChoiceFinal sampled).registers 9 = BitVec.ofNat 256 chosen.val := by
      simp [chosen]
    have outputLength : (sparseWordPairs state.outputs).length = state.used := by
      simp [sparseWordPairs, represented.outputLength]
    have outputStored : RepresentsPairs original.ram (original.registers 3) (sparseWordPairs state.outputs) := by
      rw [outputBase]
      exact represented.outputs
    have safe : ∀ index, index < 2 * (sparseWordPairs state.outputs).length →
        8 ≤ (original.registers 3 + BitVec.ofNat 256 index).toNat := by
      intro index inside
      rw [outputBase]
      exact descendingPairs_safe oracle 1 state.used index (by omega) (by simpa only [outputLength] using inside)
    have reply := freshQueryTail_value attempts original sampled cost supported
      (sparseWordPairs state.outputs) outputStored safe
    rw [outputLength] at reply
    simp only [freshChoiceValue, if_neg failed, chosenWord, Option.map_some] at reply
    have encoded := encoded_swaps (fun value : Fin size => BitVec.ofNat 256 value.val)
      (finiteWord_injective size (Nat.le_of_lt sizeFits)) state.outputs chosen
    have value : queryValue (freshQueryTail state.used (freshChoiceFinal sampled)).1 =
        some (BitVec.ofNat 256 (state.output chosen).val) := reply.trans (congrArg some encoded)
    rw [sparseForwardMemoryState_fresh state input chosen _ fresh (Nat.le_of_lt sizeFits) value]
    exact freshQuery_sample_sparse attempts original sampled cost supported oracle state represented room
      (state.input.symm input) chosen used inputBase outputBase inputValue chosenWord header failed fits

end Kriterion.ArgoMAC.ArithmeticSimulator
