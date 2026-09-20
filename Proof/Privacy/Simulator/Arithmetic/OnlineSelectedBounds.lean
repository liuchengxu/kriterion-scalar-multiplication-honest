import Proof.Privacy.Simulator.Arithmetic.OnlineCurveBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each selector key offset stays inside the original 1016 key words. -/
theorem selectedKeyOffset_bounds (index : Fin 508) (memory : Memory) :
    ∃ offset : Nat, offset < 1017 ∧
      BitVec.ofNat 256 (selectedFalseOffset index) - selectedBitWord index memory = BitVec.ofNat 256 offset := by
  have bounds : 1 ≤ selectedFalseOffset index ∧ selectedFalseOffset index < 1017 := by
    unfold selectedFalseOffset
    split <;> have bound := index.isLt <;> omega
  rw [selectedBitWord, selected_bit_mask]
  split
  · refine ⟨selectedFalseOffset index - 1, by omega, ?_⟩
    rw [show selectedFalseOffset index = (selectedFalseOffset index - 1) + 1 by omega, BitVec.ofNat_add]
    simp
  · exact ⟨selectedFalseOffset index, bounds.2, by simp⟩

/-- The fixed original-label buffer is separate from every selector input. -/
theorem onlineOriginal_disjoint (memory : Memory)
    (source : memory.registers 11 = BitVec.ofNat 256 privateBase)
    (input : memory.registers 12 = BitVec.ofNat 256 onlineInputBase)
    (output : memory.registers 14 = BitVec.ofNat 256 onlineOriginalBase) : SelectedStoreDisjoint memory := by
  intro index reached
  obtain ⟨selected, coordinate | key⟩ := reached
  · have selectedBound : selectedCoordinate selected < 5 := by
      unfold selectedCoordinate
      split <;> decide
    rw [input, output] at coordinate
    exact onlineInput_labelSeparate ⟨selectedCoordinate selected, selectedBound⟩ index
      (by simpa only [BitVec.ofNat_add] using coordinate.symm)
  · obtain ⟨offset, bound, encoded⟩ := selectedKeyOffset_bounds selected memory
    rw [source, output, encoded, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at key
    have first : onlineOriginalBase + index.val < 2 ^ 256 := by
      have small := index.isLt
      have fixed : onlineOriginalBase + 508 < 2 ^ 256 := by decide
      omega
    have second : privateBase + offset < 2 ^ 256 := by
      have fixed : privateBase + 1017 < 2 ^ 256 := by decide
      omega
    have values := congrArg BitVec.toNat key
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt first, Nat.mod_eq_of_lt second] at values
    have apart : privateBase + 1017 < onlineOriginalBase := by decide
    omega

end Kriterion.ArgoMAC.ArithmeticSimulator
