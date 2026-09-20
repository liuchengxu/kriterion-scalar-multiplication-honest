import Proof.Privacy.Simulator.Arithmetic.StoredForwardFrame
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.HashMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- A sparse memory state supplies every forward loop count, including the preserved overlay count. -/
theorem publicHandler_forwardCounts {size : Nat} (attempts : Nat) (memory : Memory)
    (oracle : Fin 15749) (state : SparsePermutation size) (pairs : List (Fin size × Fin size))
    (sparse : SparseMemory memory.ram oracle state) (overlay : OverlayMemory memory.ram oracle pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (fits : 2 * (state.used + 1) ≤ 2 ^ 110) :
    PublicBranchCounts .forward attempts state.used pairs.length memory := by
  refine ⟨(oracleLoaded_used memory oracle index).trans sparse.count, ?_⟩
  intro result supported
  exact storedForwardSamples_overlayCount attempts state.used memory result.1 result.2 supported
    oracle pairs index sparse.count overlay fits

/-- The loader returns the canonical base header in register six. -/
theorem oracleLoaded_header (memory : Memory) (oracle : Fin 15749)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val) :
    (oracleLoaded memory).registers 6 = oracleAddress oracle 0 0 := by
  simp only [show (oracleLoaded memory).registers 6 = oracleHeader (memory.registers 9) by simp [oracleLoaded],
    index, oracleHeader_address]

/-- Inverse preparation preserves permanent RAM and restores the original oracle index. -/
theorem publicInversePrepared_data (count : Nat) (memory : Memory) :
    (publicInversePrepared count memory).ram = (oracleLoaded memory).ram ∧
    (publicInversePrepared count memory).registers 9 = memory.registers 9 := by
  have unchanged := (overlayInverse_data count (oracleLoaded memory)).1
  constructor
  · exact unchanged
  · change (queryRestored (overlayInverseScan count (oracleLoaded memory)).1).registers 9 = _
    simp only [queryRestored, Function.update_of_ne (by decide : (9 : Register) ≠ 15),
      Function.update_of_ne (by decide : (9 : Register) ≠ 10), Function.update_self]
    exact (congrFun unchanged 9).trans (oracleLoaded_query memory).2.1

/-- The inverse preparation loads the correct overlay count and retains the sparse base count. -/
theorem publicHandler_inverseCounts {size : Nat} (attempts : Nat) (memory : Memory)
    (oracle : Fin 15749) (state : SparsePermutation size) (pairs : List (Fin size × Fin size))
    (sparse : SparseMemory memory.ram oracle state) (overlay : OverlayMemory memory.ram oracle pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val) :
    PublicBranchCounts .inverse attempts state.used pairs.length memory := by
  constructor
  · rw [overlayHeader_address (oracleLoaded memory) oracle (oracleLoaded_header memory oracle index)]
    rw [show (oracleLoaded memory).ram = oracleLoadRam memory from rfl]
    exact (oracleLoadRam_public memory oracle 2 0 (by decide)).trans overlay.count
  · have prepared := publicInversePrepared_data pairs.length memory
    have loaded := oracleLoaded_used (publicInversePrepared pairs.length memory) oracle (prepared.2.trans index)
    have count : (publicInversePrepared pairs.length memory).ram (oracleAddress oracle 0 0) =
        BitVec.ofNat 256 state.used := by
      rw [prepared.1]
      exact (oracleLoadRam_public memory oracle 0 0 (by decide)).trans sparse.count
    have same : (inverseLoaded (publicInversePrepared pairs.length memory)).registers 0 =
        (oracleLoaded (publicInversePrepared pairs.length memory)).registers 0 := by
      simp [inverseLoaded, metadataSwapped]
    exact same.trans (loaded.trans count)

/-- A stored hash table supplies its exact sparse lookup count. -/
theorem publicHandler_hashCounts (attempts overlayCount : Nat) (memory : Memory)
    (oracle : Fin 15749) (pairs : List (Word × Word)) (represented : HashMemory memory.ram oracle pairs)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val) :
    PublicBranchCounts .hash attempts pairs.length overlayCount memory :=
  (oracleLoaded_used memory oracle index).trans represented.count

end Kriterion.ArgoMAC.ArithmeticSimulator
