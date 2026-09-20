import Proof.Privacy.Simulator.Arithmetic.SparseInverseInstall

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The inverse answer scan retains both insertion coordinates and the exchanged table addresses. -/
theorem freshQueryTail_inverse {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 7 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 6 = BitVec.ofNat 256 outputPosition.val)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (accepted : memory.registers 7 ≠ 0#256)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (inverseCommitted (freshQueryTail state.used memory).1).ram oracle
      (state.extend room inputPosition outputPosition) := by
  rw [freshQueryTail, if_neg accepted]
  let scanned := (swapScan state.used (swapInitial (freshOutputInitial memory))).1
  have frame := freshOutputScan_frame state.used memory
  dsimp only at frame
  exact installedCommitted_inverse scanned oracle state
    (by simpa only [scanned, frame.1] using represented) room inputPosition outputPosition
    ((frame.2 0 (by decide)).trans used)
    ((frame.2 1 (by decide)).trans inputBase)
    ((frame.2 3 (by decide)).trans outputBase)
    ((congrFun frame.1 7).trans inputValue)
    ((congrFun frame.1 6).trans outputValue)
    ((congrFun frame.1 13).trans header) fits

/-- Every accepted inverse sample stores the matching extended source state. -/
theorem freshQuery_sample_inverse {size : Nat} (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseTableData original.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : original.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : original.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : original.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputValue : original.registers 8 = BitVec.ofNat 256 outputPosition.val)
    (inputValue : (freshChoiceFinal sampled).registers 9 = BitVec.ofNat 256 inputPosition.val)
    (header : original.ram 13 = oracleAddress oracle 0 0)
    (accepted : (freshChoiceFinal sampled).registers 7 ≠ 0#256)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (inverseCommitted (freshQueryTail state.used (freshChoiceFinal sampled)).1).ram oracle
      (state.extend room inputPosition outputPosition) := by
  have capacity : 2 * state.used ≤ 2 ^ 110 := by omega
  have r0 := freshChoice_metadata attempts original sampled cost supported (0 : Fin 6)
  have r1 := freshChoice_metadata attempts original sampled cost supported (1 : Fin 6)
  have r3 := freshChoice_metadata attempts original sampled cost supported (3 : Fin 6)
  have outputSaved := freshChoice_inputPosition attempts original sampled cost supported
  have inputSaved := freshChoice_outputPosition sampled accepted
  have headerSaved := freshChoice_ram attempts original sampled cost supported 13 (by decide)
  exact freshQueryTail_inverse (freshChoiceFinal sampled) oracle state
    (freshChoice_sparseData attempts original sampled cost supported oracle state represented capacity)
    room inputPosition outputPosition (r0.trans used) (r1.trans inputBase) (r3.trans outputBase)
    (inputSaved.trans inputValue) (outputSaved.trans outputValue) (headerSaved.trans header) accepted fits

/-- The inverse observer restores the original orientation of the source state. -/
def sparseInverseMemoryState {size : Nat} (state : SparsePermutation size) (input : Fin size)
    (memory : Memory) : SparsePermutation size :=
  (sparseForwardMemoryState state.reverse input memory).reverse

/-- Every fresh inverse path retains the exact source state, including cutoff failure. -/
theorem freshQuery_sample_inverseMemoryState [BN254.FieldCertificate] {size : Nat}
    (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size) (input : Fin size)
    (represented : SparseTableData original.ram oracle state)
    (fresh : ¬ (state.output.symm input).val < state.used) (sizeFits : size < 2 ^ 256)
    (used : original.registers 0 = BitVec.ofNat 256 state.used)
    (domain : original.registers 5 = BitVec.ofNat 256 size)
    (inputBase : original.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : original.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (inputValue : original.registers 8 = BitVec.ofNat 256 (state.output.symm input).val)
    (header : original.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (inverseCommitted (freshQueryTail state.used (freshChoiceFinal sampled)).1).ram oracle
      (sparseInverseMemoryState state input (freshQueryTail state.used (freshChoiceFinal sampled)).1) := by
  unfold sparseInverseMemoryState
  by_cases failed : (freshChoiceFinal sampled).registers 7 = 0#256
  · have tailFailed : (freshQueryTail state.used (freshChoiceFinal sampled)).1.registers 7 = 0#256 := by
      simp only [freshQueryTail, if_pos failed]
      exact failed
    rw [sparseForwardMemoryState_failed state.reverse input _ tailFailed, SparsePermutation.reverse_reverse,
      inverseCommitted_ram]
    exact freshQuery_failed_sparse attempts original sampled cost supported oracle state represented
      used header failed (by omega)
  · have room : state.used < size := by have := (state.output.symm input).isLt; omega
    have reached : some ((freshChoiceFinal sampled).registers 9) ∈
        ((freshChoiceSamples attempts original).map
          (fun result => freshChoiceValue (freshChoiceFinal result.1))).support := by
      apply (PMF.mem_support_map_iff _ _ _).mpr
      exact ⟨(sampled, cost), supported, by simp [freshChoiceValue, failed]⟩
    have bound := freshChoice_chosen_bounds attempts size state.used original
      ((freshChoiceFinal sampled).registers 9) room (Nat.le_of_lt sizeFits) domain used reached
    let chosen : Fin size := ⟨((freshChoiceFinal sampled).registers 9).toNat, bound.2⟩
    have chosenWord : (freshChoiceFinal sampled).registers 9 = BitVec.ofNat 256 chosen.val := by simp [chosen]
    have inputLength : (sparseWordPairs state.inputs).length = state.used := by
      simp [sparseWordPairs, represented.inputLength]
    have inputStored : RepresentsPairs original.ram (original.registers 3) (sparseWordPairs state.inputs) := by
      rw [outputBase]
      exact represented.inputs
    have safe : ∀ index, index < 2 * (sparseWordPairs state.inputs).length →
        8 ≤ (original.registers 3 + BitVec.ofNat 256 index).toNat := by
      intro index inside
      rw [outputBase]
      exact descendingPairs_safe oracle 0 state.used index (by omega) (by simpa only [inputLength] using inside)
    have reply := freshQueryTail_value attempts original sampled cost supported (sparseWordPairs state.inputs) inputStored safe
    rw [inputLength] at reply
    simp only [freshChoiceValue, if_neg failed, chosenWord, Option.map_some] at reply
    have encoded := encoded_swaps (fun value : Fin size => BitVec.ofNat 256 value.val)
      (finiteWord_injective size (Nat.le_of_lt sizeFits)) state.inputs chosen
    have value : queryValue (freshQueryTail state.used (freshChoiceFinal sampled)).1 =
        some (BitVec.ofNat 256 (state.reverse.output chosen).val) := reply.trans (congrArg some encoded)
    rw [sparseForwardMemoryState_fresh state.reverse input chosen _ fresh (Nat.le_of_lt sizeFits) value]
    exact freshQuery_sample_inverse attempts original sampled cost supported oracle state represented room
      chosen (state.output.symm input) used inputBase outputBase inputValue chosenWord header failed fits

end Kriterion.ArgoMAC.ArithmeticSimulator
