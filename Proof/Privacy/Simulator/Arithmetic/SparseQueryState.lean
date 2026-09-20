import Proof.Privacy.Simulator.Arithmetic.SparseMemory
import Proof.Privacy.Simulator.Arithmetic.PermutationForward
import Proof.Privacy.Simulator.Arithmetic.FreshQuerySource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The retry sampler preserves every public cell on every sampled path. -/
theorem freshChoice_public (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (freshChoiceFinal sampled).ram (oracleAddress oracle table offset) =
      original.ram (oracleAddress oracle table offset) := by
  apply freshChoice_ram attempts original sampled cost supported
  rw [oracleAddress_value oracle table offset fits]
  exact le_trans (by decide : 8 ≤ 2 ^ 128) (oracleCell_bounds oracle table offset fits).1

/-- Every retry path retains both complete sparse tables. -/
theorem freshChoice_sparseData {size : Nat} (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseTableData original.ram oracle state) (fits : 2 * state.used ≤ 2 ^ 110) :
    SparseTableData (freshChoiceFinal sampled).ram oracle state :=
  SparseTableData.congr original.ram _ oracle state represented fits
    (freshChoice_public attempts original sampled cost supported oracle)

/-- Every retry path retains the persistent sparse header and both tables. -/
theorem freshChoice_sparseMemory {size : Nat} (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseMemory original.ram oracle state) (fits : 2 * state.used ≤ 2 ^ 110) :
    SparseMemory (freshChoiceFinal sampled).ram oracle state :=
  ⟨freshChoice_sparseData attempts original sampled cost supported oracle state represented.toSparseTableData fits,
    (freshChoice_public attempts original sampled cost supported oracle 0 0 (by decide)).trans represented.count⟩

/-- The retry path retains the inverse input position in scratch cell six. -/
theorem freshChoice_inputPosition (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support) :
    (freshChoiceFinal sampled).ram 6 = original.registers 8 := by
  have saved : sampled.ram = (oracleSaved original).ram :=
    (runtimeSamplerMemory_data _ _ _ sampled cost supported).2
  by_cases failed : sampled.registers 7 = 0#256 <;>
    simp [freshChoiceFinal, oracleRestored, saved, oracleSaved, failed]

/-- A successful retry stores its selected suffix position in scratch cell seven. -/
theorem freshChoice_outputPosition (sampled : Memory)
    (accepted : (freshChoiceFinal sampled).registers 7 ≠ 0#256) :
    (freshChoiceFinal sampled).ram 7 = (freshChoiceFinal sampled).registers 9 := by
  by_cases failed : sampled.registers 7 = 0#256
  · simp [freshChoiceFinal, oracleRestored, failed] at accepted
  · simp [freshChoiceFinal, oracleRestored, failed]

/-- The answer scan preserves the sparse metadata and stored positions needed by installation. -/
theorem freshOutputScan_frame (count : Nat) (memory : Memory) :
    let scanned := (swapScan count (swapInitial (freshOutputInitial memory))).1
    scanned.ram = memory.ram ∧ ∀ register : Register, register.val < 6 →
      scanned.registers register = memory.registers register := by
  refine ⟨(swapScan_data _ _).2, ?_⟩
  intro register small
  rw [swapScan_caller _ _ register (by omega)]
  have n6 : register ≠ 6 := by intro equal; subst register; norm_num at small
  have n8 : register ≠ 8 := by intro equal; subst register; norm_num at small
  have n9 : register ≠ 9 := by intro equal; subst register; norm_num at small
  have n10 : register ≠ 10 := by intro equal; subst register; norm_num at small
  have n14 : register ≠ 14 := by intro equal; subst register; norm_num at small
  simp [swapInitial, freshOutputInitial, n6, n8, n9, n10, n14]

/-- An accepted fresh tail and its commit represent the complete extended sparse source state. -/
theorem freshQueryTail_sparse {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 6 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 7 = BitVec.ofNat 256 outputPosition.val)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (accepted : memory.registers 7 ≠ 0#256)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (freshQueryTail state.used memory).1).ram oracle
      (state.extend room inputPosition outputPosition) := by
  rw [freshQueryTail, if_neg accepted]
  let scanned := (swapScan state.used (swapInitial (freshOutputInitial memory))).1
  have frame := freshOutputScan_frame state.used memory
  dsimp only at frame
  exact installedCommitted_sparse scanned oracle state
    (by simpa only [scanned, frame.1] using represented) room inputPosition outputPosition
    ((frame.2 0 (by decide)).trans used)
    ((frame.2 1 (by decide)).trans inputBase)
    ((frame.2 3 (by decide)).trans outputBase)
    ((congrFun frame.1 6).trans inputValue)
    ((congrFun frame.1 7).trans outputValue)
    ((congrFun frame.1 13).trans header) fits

/-- A known query preserves the complete sparse memory relation. -/
theorem knownQuery_sparse {size : Nat} (inputCount outputCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseMemory memory.ram oracle state) :
    SparseMemory (knownQueryScan inputCount outputCount memory).1.ram oracle state := by
  rw [(knownQueryScan_data inputCount outputCount memory).1]
  exact represented

end Kriterion.ArgoMAC.ArithmeticSimulator
