import Proof.Privacy.Simulator.Arithmetic.InstallFreshLayout
import Proof.Privacy.Simulator.Arithmetic.HashProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
open Security.OperationalOracle

/-- The RAM representation stores each finite transposition as two machine words. -/
def sparseWordPairs {size : Nat} (pairs : List (Fin size × Fin size)) : List (Word × Word) :=
  pairs.map fun pair => (BitVec.ofNat 256 pair.1.val, BitVec.ofNat 256 pair.2.val)

/-- Both sparse lists occupy their canonical descending public table regions. -/
structure SparseTableData {size : Nat} (ram : Word → Word) (oracle : Fin 15749)
    (state : SparsePermutation size) : Prop where
  inputLength : state.inputs.length = state.used
  outputLength : state.outputs.length = state.used
  inputs : RepresentsPairs ram (oracleAddress oracle 0 (2 ^ 110 - 2 * state.used)) (sparseWordPairs state.inputs)
  outputs : RepresentsPairs ram (oracleAddress oracle 1 (2 ^ 110 - 2 * state.used)) (sparseWordPairs state.outputs)

/-- The sparse memory relation includes the persistent used-count header. -/
structure SparseMemory {size : Nat} (ram : Word → Word) (oracle : Fin 15749)
    (state : SparsePermutation size) : Prop extends SparseTableData ram oracle state where
  count : ram (oracleAddress oracle 0 0) = BitVec.ofNat 256 state.used

/-- The metadata loader preserves every public table cell. -/
theorem oracleLoadRam_public (memory : Memory) (oracle : Fin 15749) (table : Fin 4) (offset : Nat)
    (fits : offset < 2 ^ 110) :
    oracleLoadRam memory (oracleAddress oracle table offset) = memory.ram (oracleAddress oracle table offset) := by
  have d9 := oracleAddress_private_disjoint oracle table offset 9 fits (by decide)
  have d12 := oracleAddress_private_disjoint oracle table offset 12 fits (by decide)
  have d13 := oracleAddress_private_disjoint oracle table offset 13 fits (by decide)
  simp [oracleLoadRam, d9, d12, d13]

/-- RAM agreement on public cells preserves both represented sparse lists. -/
theorem SparseTableData.congr {size : Nat} (original updated : Word → Word) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData original oracle state)
    (fits : 2 * state.used ≤ 2 ^ 110)
    (same : ∀ table offset, offset < 2 ^ 110 →
      updated (oracleAddress oracle table offset) = original (oracleAddress oracle table offset)) :
    SparseTableData updated oracle state := by
  refine ⟨represented.inputLength, represented.outputLength, ?_, ?_⟩
  · apply RepresentsPairs.congr _ original updated _ represented.inputs
    intro index bound
    have length : (sparseWordPairs state.inputs).length = state.used := by
      simp [sparseWordPairs, represented.inputLength]
    rw [length] at bound
    rw [oracleAddress_add]
    exact same 0 _ (by omega)
  · apply RepresentsPairs.congr _ original updated _ represented.outputs
    intro index bound
    have length : (sparseWordPairs state.outputs).length = state.used := by
      simp [sparseWordPairs, represented.outputLength]
    rw [length] at bound
    rw [oracleAddress_add]
    exact same 1 _ (by omega)

/-- The metadata loader retains the complete sparse memory relation. -/
theorem SparseMemory.loaded {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseMemory memory.ram oracle state)
    (fits : 2 * state.used ≤ 2 ^ 110) : SparseMemory (oracleLoaded memory).ram oracle state := by
  refine ⟨SparseTableData.congr memory.ram (oracleLoadRam memory) oracle state
    represented.toSparseTableData fits (oracleLoadRam_public memory oracle), ?_⟩
  exact (oracleLoadRam_public memory oracle 0 0 (by decide)).trans represented.count

/-- The empty sparse state has no table entries and a zero header. -/
theorem SparseMemory.empty (ram : Word → Word) (oracle : Fin 15749) (size : Nat)
    (count : ram (oracleAddress oracle 0 0) = 0#256) :
    SparseMemory ram oracle (SparsePermutation.empty size) := by
  exact ⟨⟨rfl, rfl, trivial, trivial⟩, count⟩

/-- Fresh installation represents both extended source transposition lists. -/
theorem installedFresh_sparseData {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 6 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 7 = BitVec.ofNat 256 outputPosition.val)
    (fits : 2 * (state.used + 1) ≤ 2 ^ 110) :
    SparseTableData (installedFresh memory).ram oracle (state.extend room inputPosition outputPosition) := by
  have installed := installedFresh_layout memory oracle state.used
    (sparseWordPairs state.inputs) (sparseWordPairs state.outputs)
    (by simp [sparseWordPairs, represented.inputLength])
    (by simp [sparseWordPairs, represented.outputLength]) inputBase outputBase
    (by simpa only [inputBase] using represented.inputs)
    (by simpa only [outputBase] using represented.outputs) fits
  have newInput : (installedFresh memory).registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * (state.used + 1)) := by
    simp only [show (installedFresh memory).registers 1 = memory.registers 1 - 2#256 by simp [installedFresh]]
    rw [inputBase, oracleAddress_prepend oracle 0 state.used fits]
  have newOutput : (installedFresh memory).registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * (state.used + 1)) := by
    simp only [show (installedFresh memory).registers 3 = memory.registers 3 - 2#256 by simp [installedFresh]]
    rw [outputBase, oracleAddress_prepend oracle 1 state.used fits]
  refine ⟨by simp [SparsePermutation.extend, represented.inputLength],
    by simp [SparsePermutation.extend, represented.outputLength], ?_, ?_⟩
  · simpa only [SparsePermutation.extend, sparseWordPairs, List.map_cons, newInput, used, inputValue] using installed.1
  · simpa only [SparsePermutation.extend, sparseWordPairs, List.map_cons, newOutput, used, outputValue] using installed.2

/-- The explicit count commit preserves both sparse lists and sets their matching header. -/
theorem oracleCommitted_sparse {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * state.used + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted memory).ram oracle state := by
  refine ⟨⟨represented.inputLength, represented.outputLength, ?_, ?_⟩, ?_⟩
  · apply oracleCommitted_pairs memory _ _ represented.inputs
    intro index bound
    rw [header]
    apply descendingPairs_header_disjoint oracle 0 state.used index fits
    simpa [sparseWordPairs, represented.inputLength] using bound
  · apply oracleCommitted_pairs memory _ _ represented.outputs
    intro index bound
    rw [header]
    apply descendingPairs_header_disjoint oracle 1 state.used index fits
    simpa [sparseWordPairs, represented.outputLength] using bound
  · simp only [oracleCommitted]
    rw [← header]
    simp only [Function.update_self, used]

/-- Fresh installation preserves every scratch and private RAM cell. -/
theorem installedFresh_private (memory : Memory) (oracle : Fin 15749) (count cell : Nat)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) ≤ 2 ^ 110) (privateBound : cell < 2 ^ 96) :
    (installedFresh memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have startBound : 2 ^ 110 - 2 * (count + 1) < 2 ^ 110 := by omega
  have nextBound : 2 ^ 110 - 2 * (count + 1) + 1 < 2 ^ 110 := by omega
  apply installedFresh_other memory
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle 0 _ cell startBound privateBound)
  · rw [inputBase, oracleAddress_prepend oracle 0 count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle 0 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle 0 _ cell nextBound privateBound)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    exact Ne.symm (oracleAddress_private_disjoint oracle 1 _ cell startBound privateBound)
  · rw [outputBase, oracleAddress_prepend oracle 1 count fits]
    change BitVec.ofNat 256 cell ≠ oracleAddress oracle 1 _ + BitVec.ofNat 256 1
    rw [oracleAddress_add]
    exact Ne.symm (oracleAddress_private_disjoint oracle 1 _ cell nextBound privateBound)

/-- Fresh installation and the explicit count commit represent the complete extended source state. -/
theorem installedCommitted_sparse {size : Nat} (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation size) (represented : SparseTableData memory.ram oracle state)
    (room : state.used < size) (inputPosition outputPosition : Fin size)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * state.used))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * state.used))
    (inputValue : memory.ram 6 = BitVec.ofNat 256 inputPosition.val)
    (outputValue : memory.ram 7 = BitVec.ofNat 256 outputPosition.val)
    (header : memory.ram 13 = oracleAddress oracle 0 0)
    (fits : 2 * (state.used + 1) + 256 < 2 ^ 110) :
    SparseMemory (oracleCommitted (installedFresh memory)).ram oracle
      (state.extend room inputPosition outputPosition) := by
  have capacity : 2 * (state.used + 1) ≤ 2 ^ 110 := by omega
  apply oracleCommitted_sparse (installedFresh memory) oracle _
    (installedFresh_sparseData memory oracle state represented room inputPosition outputPosition
      used inputBase outputBase inputValue outputValue capacity)
  · simp [installedFresh, SparsePermutation.extend, used, BitVec.ofNat_add]
  · exact (installedFresh_private memory oracle state.used 13 inputBase outputBase capacity (by decide)).trans header
  · exact fits

end Kriterion.ArgoMAC.ArithmeticSimulator
