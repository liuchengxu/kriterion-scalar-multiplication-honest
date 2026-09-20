import Proof.Privacy.Simulator.Arithmetic.SparseQueryState

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Every accepted fresh sample installs the matching extended source state. -/
theorem freshQuery_sample_sparse {size : Nat} (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseTableData original.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : original.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : original.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : original.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputValue : original.registers 8 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : (freshChoiceFinal sampled).registers 9 = BitVec.ofNat 256 outputPosition.val)
    (header : original.ram 13 = oracleAddress oracle 0 0)
    (accepted : (freshChoiceFinal sampled).registers 7 ≠ 0#256)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (freshQueryTail state.used (freshChoiceFinal sampled)).1).ram oracle
      (state.extend room inputPosition outputPosition) := by
  have capacity : 2 * state.used ≤ 2 ^ 110 := by omega
  have r0 := freshChoice_metadata attempts original sampled cost supported (0 : Fin 6)
  have r1 := freshChoice_metadata attempts original sampled cost supported (1 : Fin 6)
  have r3 := freshChoice_metadata attempts original sampled cost supported (3 : Fin 6)
  have inputSaved := freshChoice_inputPosition attempts original sampled cost supported
  have outputSaved := freshChoice_outputPosition sampled accepted
  have headerSaved := freshChoice_ram attempts original sampled cost supported 13 (by decide)
  exact freshQueryTail_sparse (freshChoiceFinal sampled) oracle state
    (freshChoice_sparseData attempts original sampled cost supported oracle state represented capacity)
    room inputPosition outputPosition (r0.trans used) (r1.trans inputBase) (r3.trans outputBase)
    (inputSaved.trans inputValue) (outputSaved.trans outputValue) (headerSaved.trans header) accepted fits

/-- A failed fresh sample preserves the source state through the count commit. -/
theorem freshQuery_failed_sparse {size : Nat} (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseTableData original.ram oracle state)
    (used : original.registers 0 = BitVec.ofNat 256 state.used)
    (header : original.ram 13 = oracleAddress oracle 0 0)
    (failed : (freshChoiceFinal sampled).registers 7 = 0#256)
    (fits : 2 * state.used + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (freshQueryTail state.used (freshChoiceFinal sampled)).1).ram oracle state := by
  rw [freshQueryTail, if_pos failed]
  have r0 := freshChoice_metadata attempts original sampled cost supported (0 : Fin 6)
  have headerSaved := freshChoice_ram attempts original sampled cost supported 13 (by decide)
  exact oracleCommitted_sparse (freshChoiceFinal sampled) oracle state
    (freshChoice_sparseData attempts original sampled cost supported oracle state represented (by omega))
    (r0.trans used) (headerSaved.trans header) fits

/-- The committed known-query state retains the same sparse source state. -/
theorem knownQuery_committed_sparse {size : Nat} (count : Nat) (memory : Memory)
    (oracle : Fin 15749) (state : SparsePermutation size)
    (represented : SparseTableData memory.ram oracle state)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * state.used + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (knownQueryScan count count memory).1).ram oracle state := by
  have same := (knownQueryScan_data count count memory).1
  exact oracleCommitted_sparse _ oracle state (by simpa only [same] using represented)
    ((knownQueryScan_metadata count count memory 0 (by decide)).trans used)
    ((congrFun same 13).trans header) fits

end Kriterion.ArgoMAC.ArithmeticSimulator
