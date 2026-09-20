import Proof.Privacy.Simulator.Arithmetic.HistoryMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The overlay append writes only its two new words and count header. -/
theorem overlayAppended_ram (memory : Memory) :
    (overlayAppended memory).ram =
      Function.update (Function.update (Function.update memory.ram
        (overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256))
        (memory.registers 8))
        (overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256) + 1#256)
        (memory.ram 14)) (overlayHeader memory) (memory.ram (overlayHeader memory) + 1#256) := by
  simp [overlayAppended, overlayAppendFinished, pairStored, overlayAppendReady]

/-- The selected overlay append preserves each other public table region. -/
theorem overlayAppended_publicFrame (memory : Memory) (oracle other : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (region : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (separate : other ≠ oracle ∨ region ≠ 2) :
    (overlayAppended memory).ram (oracleAddress other region offset) =
      memory.ram (oracleAddress other region offset) := by
  have selected := overlayHeader_address memory oracle header
  have cursor : overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256) =
      oracleAddress oracle 2 (256 + 2 * count) := by
    rw [selected, counter, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, oracleAddress_add]
    congr 1
    omega
  have range : overlayHeader memory + (memory.ram (overlayHeader memory) * 2#256 + 256#256) + 1#256 =
      oracleAddress oracle 2 (257 + 2 * count) := by
    rw [cursor]
    change oracleAddress oracle 2 _ + BitVec.ofNat 256 1 = _
    rw [oracleAddress_add]
    congr 1
    omega
  have apart : ∀ target, target < 2 ^ 110 →
      oracleAddress other region offset ≠ oracleAddress oracle 2 target := by
    intro target targetFits equal
    have eqs := oracleAddress_injective other oracle region 2 offset target offsetFits targetFits equal
    exact separate.elim (fun neq => neq eqs.1) (fun neq => neq eqs.2.1)
  rw [overlayAppended_ram, range, cursor, selected]
  simp only [Function.update_of_ne (apart 0 (by decide)),
    Function.update_of_ne (apart (257 + 2 * count) capacity),
    Function.update_of_ne (apart (256 + 2 * count) (by omega))]

/-- The selected history append preserves each other public table region. -/
theorem historyAppended_publicFrame (memory : Memory) (oracle other : Fin 15749) (count : Nat)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 3 0) = BitVec.ofNat 256 count)
    (capacity : 257 + 2 * count < 2 ^ 110) (region : Fin 4) (offset : Nat)
    (offsetFits : offset < 2 ^ 110) (separate : other ≠ oracle ∨ region ≠ 3) :
    (historyAppended memory).ram (oracleAddress other region offset) =
      memory.ram (oracleAddress other region offset) := by
  rcases publicHistoryResult_addresses memory oracle count header counter with ⟨selected, domain, range⟩
  have apart : ∀ target, target < 2 ^ 110 →
      oracleAddress other region offset ≠ oracleAddress oracle 3 target := by
    intro target targetFits equal
    have eqs := oracleAddress_injective other oracle region 3 offset target offsetFits targetFits equal
    exact separate.elim (fun neq => neq eqs.1) (fun neq => neq eqs.2.1)
  rw [historyAppended_ram, range, domain, selected]
  simp only [Function.update_of_ne (apart 0 (by decide)),
    Function.update_of_ne (apart (257 + 2 * count) capacity),
    Function.update_of_ne (apart (256 + 2 * count) (by omega))]

/-- The overlay append preserves every selected sparse base entry. -/
theorem overlayAppended_sparseMemory (memory : Memory) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (count : Nat)
    (represented : SparseMemory memory.ram oracle state)
    (header : memory.registers 6 = oracleAddress oracle 0 0)
    (counter : memory.ram (oracleAddress oracle 2 0) = BitVec.ofNat 256 count)
    (fits : 2 * state.used ≤ 2 ^ 110) (capacity : 257 + 2 * count < 2 ^ 110) :
    SparseMemory (overlayAppended memory).ram oracle state := by
  refine ⟨⟨represented.inputLength, represented.outputLength, ?_, ?_⟩, ?_⟩
  · apply RepresentsPairs.congr _ memory.ram _ _ represented.inputs
    intro index bound
    have len : (sparseWordPairs state.inputs).length = state.used := by
      simp only [sparseWordPairs, List.length_map, represented.inputLength]
    rw [len] at bound
    rw [oracleAddress_add]
    exact overlayAppended_publicFrame memory oracle oracle count header counter capacity 0 _ (by omega) (Or.inr (by decide))
  · apply RepresentsPairs.congr _ memory.ram _ _ represented.outputs
    intro index bound
    have len : (sparseWordPairs state.outputs).length = state.used := by
      simp only [sparseWordPairs, List.length_map, represented.outputLength]
    rw [len] at bound
    rw [oracleAddress_add]
    exact overlayAppended_publicFrame memory oracle oracle count header counter capacity 1 _ (by omega) (Or.inr (by decide))
  · exact (overlayAppended_publicFrame memory oracle oracle count header counter capacity 0 0
      (by decide) (Or.inr (by decide))).trans represented.count

end Kriterion.ArgoMAC.ArithmeticSimulator
