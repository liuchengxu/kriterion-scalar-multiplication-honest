import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsProtocol

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

/-- The x-coordinate labels need only the input-key buffer. -/
theorem inputKey_x_key (key : InputMacKey) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1 (inputKeySchedule.words key)) (i : Fin 254) :
    ram (pointer + BitVec.ofNat 256 (509 + 2 * i.val)) = (key.x.get i).trueLabel.setWidth 256 ∧
    ram (pointer + BitVec.ofNat 256 (510 + 2 * i.val)) = (key.x.get i).falseLabel.setWidth 256 := by
  have keys := inputKey_x_words key ram pointer 1 stored
  have selected := wordsAt_scheduleVector keySchedule 254 key.x ram pointer 509 i keys
  have result := wordsAt_key ram pointer (509 + 2 * i.val) (key.x.get i) selected
  simpa only [show 509 + 2 * i.val + 1 = 510 + 2 * i.val by omega] using result

/-- The y-coordinate labels need only the input-key buffer. -/
theorem inputKey_y_key (key : InputMacKey) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1 (inputKeySchedule.words key)) (i : Fin 254) :
    ram (pointer + BitVec.ofNat 256 (1 + 2 * i.val)) = (key.y.get i).trueLabel.setWidth 256 ∧
    ram (pointer + BitVec.ofNat 256 (2 + 2 * i.val)) = (key.y.get i).falseLabel.setWidth 256 := by
  have keys := inputKey_y_words key ram pointer 1 stored
  have selected := wordsAt_scheduleVector keySchedule 254 key.y ram pointer 1 i keys
  have result := wordsAt_key ram pointer (1 + 2 * i.val) (key.y.get i) selected
  simpa only [show 1 + 2 * i.val + 1 = 2 + 2 * i.val by omega] using result

/-- The arithmetic selector equals the original selected-label definition. -/
theorem selectedLabelWord_keySource [BN254.FieldCertificate] (key : InputMacKey) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 1 (inputKeySchedule.words key))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) (index : Fin 508) :
    selectedLabelWord index base = ((Lamport.selectedLabels (key.encodeAffine input)).get index).setWidth 256 := by
  by_cases low : index.val < 254
  · let bit : Fin 254 := ⟨index.val, low⟩
    have keys := inputKey_x_key key base.ram (base.registers 11) stored bit
    have mask : selectedBitWord index base = if (coordinateBits input.x).getLsb bit then 1 else 0 := by
      simp only [selectedBitWord, selectedCoordinate, selectedBit, if_pos low, BitVec.add_zero, coordinates.1]
      exact (selected_bit_mask _ index.val).trans (congrArg (fun value : Bool => if value then (1 : Word) else 0) (coordinate_word_bit input.x bit))
    have prior : BitVec.ofNat 256 (510 + 2 * index.val) - 1#256 = BitVec.ofNat 256 (509 + 2 * index.val) := by
      rw [show 510 + 2 * index.val = (509 + 2 * index.val) + 1 by omega, BitVec.ofNat_add]
      simp
    rw [selectedLabelWord, mask, selectedLabels_low _ _ index low]
    change base.ram (base.registers 11 + (BitVec.ofNat 256 (selectedFalseOffset index) -
      (if (coordinateBits input.x).getLsb bit then 1 else 0))) =
      (BitAdaptor.encode (key.x.get bit) ((coordinateBits input.x).getLsb bit)).setWidth 256
    cases chosen : (coordinateBits input.x).getLsb bit <;>
      simp [selectedFalseOffset, low, prior, keys.1, keys.2, BitAdaptor.encode, bit]
  · let bit : Fin 254 := ⟨index.val - 254, by change index.val - 254 < 254; have bound := index.isLt; omega⟩
    have keys := inputKey_y_key key base.ram (base.registers 11) stored bit
    have mask : selectedBitWord index base = if (coordinateBits input.y).getLsb bit then 1 else 0 := by
      have coordinate : base.ram (base.registers 12 + 1#256) = BitVec.ofNat 256 input.y.val := by
        simpa only [BitVec.ofNat_eq_ofNat] using coordinates.2
      simp only [selectedBitWord, selectedCoordinate, selectedBit, if_neg low, coordinate]
      exact (selected_bit_mask _ (index.val - 254)).trans
        (congrArg (fun value : Bool => if value then (1 : Word) else 0) (coordinate_word_bit input.y bit))
    have prior : BitVec.ofNat 256 (2 + 2 * (index.val - 254)) - 1#256 = BitVec.ofNat 256 (1 + 2 * (index.val - 254)) := by
      rw [show 2 + 2 * (index.val - 254) = (1 + 2 * (index.val - 254)) + 1 by omega, BitVec.ofNat_add]
      simp
    rw [selectedLabelWord, mask, selectedLabels_high _ _ index low]
    change base.ram (base.registers 11 + (BitVec.ofNat 256 (selectedFalseOffset index) -
      (if (coordinateBits input.y).getLsb bit then 1 else 0))) =
      (BitAdaptor.encode (key.y.get bit) ((coordinateBits input.y).getLsb bit)).setWidth 256
    cases chosen : (coordinateBits input.y).getLsb bit <;>
      simp [selectedFalseOffset, low, prior, keys.1, keys.2, BitAdaptor.encode, bit]

end Kriterion.ArgoMAC.ArithmeticSimulator
