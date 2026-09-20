import Proof.Privacy.Simulator.Arithmetic.SparseFreshMemory
import Proof.Privacy.Simulator.Arithmetic.StoredInverse

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Pair insertion works in either order of two distinct public table regions. -/
theorem installedFresh_regions (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (inputRegion outputRegion : Fin 4) (separate : inputRegion ≠ outputRegion)
    (inputs outputs : List (Word × Word)) (inputLength : inputs.length = count) (outputLength : outputs.length = count)
    (inputBase : memory.registers 1 = oracleAddress oracle inputRegion (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle outputRegion (2 ^ 110 - 2 * count))
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 1)
      ((memory.registers 0, memory.ram 6) :: inputs) ∧
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 3)
      ((memory.registers 0, memory.ram 7) :: outputs) := by
  apply installedFresh_represents memory inputs outputs inputStored outputStored
  · rw [inputLength]
    have upper : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  · rw [outputLength]
    have upper : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  · intro first firstFits second secondFits
    rw [inputBase, outputBase, oracleAddress_prepend oracle inputRegion count fits,
      oracleAddress_prepend oracle outputRegion count fits]
    exact descendingPairs_disjoint oracle inputRegion outputRegion separate (count + 1) (count + 1) fits fits
      first second (by simpa [inputLength] using firstFits) (by simpa [outputLength] using secondFits)

/-- Pair insertion in either public region order preserves private and scratch RAM. -/
theorem installedFresh_regions_private (memory : Memory) (oracle : Fin 15749) (count cell : Nat)
    (inputRegion outputRegion : Fin 4)
    (inputBase : memory.registers 1 = oracleAddress oracle inputRegion (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle outputRegion (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (privateBound : cell < 2 ^ 96) :
    (installedFresh memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have startBound : 2 ^ 110 - 2 * (count + 1) < 2 ^ 110 := by omega
  have nextBound : 2 ^ 110 - 2 * (count + 1) + 1 < 2 ^ 110 := by omega
  apply installedFresh_other memory
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle inputRegion _ cell startBound privateBound)
  · rw [inputBase, oracleAddress_prepend oracle inputRegion count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle inputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle inputRegion _ cell nextBound privateBound)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle outputRegion _ cell startBound privateBound)
  · rw [outputBase, oracleAddress_prepend oracle outputRegion count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle outputRegion _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle outputRegion _ cell nextBound privateBound)

/-- The inverse insertion stores the chosen input and the queried output in their original regions. -/
theorem installedFresh_inverseData {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 7 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 6 = BitVec.ofNat 256 outputPosition.val)
    (fits : 2 * (state.used + 1) ≤ 2 ^ 110) :
    SparseTableData (installedFresh memory).ram oracle (state.extend room inputPosition outputPosition) := by
  have installed := installedFresh_regions memory oracle state.used 1 0 (by decide)
    (sparseWordPairs state.outputs) (sparseWordPairs state.inputs)
    (by simp [sparseWordPairs, represented.outputLength])
    (by simp [sparseWordPairs, represented.inputLength]) inputBase outputBase
    (by simpa only [inputBase] using represented.outputs)
    (by simpa only [outputBase] using represented.inputs) fits
  have newInput : (installedFresh memory).registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * (state.used + 1)) := by
    simp only [show (installedFresh memory).registers 3 = memory.registers 3 - 2#256 by simp [installedFresh]]
    rw [outputBase, oracleAddress_prepend oracle 0 state.used fits]
  have newOutput : (installedFresh memory).registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * (state.used + 1)) := by
    simp only [show (installedFresh memory).registers 1 = memory.registers 1 - 2#256 by simp [installedFresh]]
    rw [inputBase, oracleAddress_prepend oracle 1 state.used fits]
  refine ⟨by simp [SparsePermutation.extend, represented.inputLength],
    by simp [SparsePermutation.extend, represented.outputLength], ?_, ?_⟩
  · simpa only [SparsePermutation.extend, sparseWordPairs, List.map_cons, newInput, used, inputValue] using installed.2
  · simpa only [SparsePermutation.extend, sparseWordPairs, List.map_cons, newOutput, used, outputValue] using installed.1

/-- The inverse commit writes the same RAM count as the ordinary commit. -/
theorem inverseCommitted_ram (memory : Memory) :
    (inverseCommitted memory).ram = (oracleCommitted memory).ram := by
  simp [inverseCommitted, oracleCommitted, metadataSwapped]

/-- The inverse insertion and count commit store the exact extended source state. -/
theorem installedCommitted_inverse {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 7 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 6 = BitVec.ofNat 256 outputPosition.val)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (inverseCommitted (installedFresh memory)).ram oracle
      (state.extend room inputPosition outputPosition) := by
  rw [inverseCommitted_ram]
  have capacity : 2 * (state.used + 1) ≤ 2 ^ 110 := by omega
  apply oracleCommitted_sparse (installedFresh memory) oracle _
    (installedFresh_inverseData memory oracle state represented room inputPosition outputPosition
      used inputBase outputBase inputValue outputValue capacity)
  · simp [installedFresh, SparsePermutation.extend, used, BitVec.ofNat_add]
  · exact (installedFresh_regions_private memory oracle state.used 13 1 0 inputBase outputBase capacity (by decide)).trans header
  · exact fits

end Kriterion.ArgoMAC.ArithmeticSimulator
