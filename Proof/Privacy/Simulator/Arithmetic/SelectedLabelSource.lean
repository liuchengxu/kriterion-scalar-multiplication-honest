import Proof.Privacy.Simulator.Arithmetic.SelectedLabelSegment
import Proof.Privacy.Simulator.Arithmetic.InputKeyLayout
import Proof.Privacy.Simulator.Arithmetic.OnlineInputProtocol

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling

/-- A right shift and one-bit mask return exactly zero or one. -/
theorem selected_bit_mask (value : Word) (bit : Nat) :
    (value >>> bit) &&& 1 = if value.getLsbD bit then 1 else 0 := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.and_one_eq_setWidth_ofBool_getLsbD,
    BitVec.getLsbD_ushiftRight, Nat.add_zero]
  cases value.getLsbD bit <;> rfl

/-- The input word and the source coordinate use the same low 254 bits. -/
theorem coordinate_word_bit (value : BN254.BaseField) (bit : Fin 254) :
    (BitVec.ofNat 256 value.val).getLsbD bit.val = (coordinateBits value).getLsb bit := by
  change (BitVec.ofNat 256 value.val).getLsbD bit.val = (coordinateBits value).getLsbD bit.val
  simp only [coordinateBits, BitVec.getLsbD_ofNat]
  simp [bit.isLt, show bit.val < 256 by have bound := bit.isLt; omega]

/-- The two input coordinates remain available in the parsed online record. -/
theorem onlineInput_coordinates [BN254.FieldCertificate] (base : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) :
    (onlineInputMemory base input output rest).ram (base.registers 10) = BitVec.ofNat 256 input.x.val ∧
    (onlineInputMemory base input output rest).ram (base.registers 10 + 1) = BitVec.ofNat 256 input.y.val := by
  rw [(onlineInputMemory_values base input output rest).1]
  simp [onlineRecordRam]

/-- The low signature indices select the original x-coordinate labels. -/
theorem selectedLabels_low (key : InputMacKey) (input : BN254.AffineInput) (index : Fin 508) (low : index.val < 254) :
    (Lamport.selectedLabels (key.encodeAffine input)).get index =
      BitAdaptor.encode (key.x.get ⟨index.val, low⟩) ((coordinateBits input.x).getLsb ⟨index.val, low⟩) := by
  simp only [Lamport.selectedLabels, Vector.get_ofFn, dif_pos low, InputMacKey.encodeAffine,
    InputMacKey.encode, encodeCoordinate, BitInput.ofAffine, Vector.get_ofFn]
  rfl

/-- The high signature indices select the original y-coordinate labels. -/
theorem selectedLabels_high (key : InputMacKey) (input : BN254.AffineInput) (index : Fin 508) (high : ¬index.val < 254) :
    (Lamport.selectedLabels (key.encodeAffine input)).get index =
      BitAdaptor.encode (key.y.get ⟨index.val - 254, by change index.val - 254 < 254; have bound := index.isLt; omega⟩)
        ((coordinateBits input.y).getLsb ⟨index.val - 254, by change index.val - 254 < 254; have bound := index.isLt; omega⟩) := by
  simp only [Lamport.selectedLabels, Vector.get_ofFn, dif_neg high, InputMacKey.encodeAffine,
    InputMacKey.encode, encodeCoordinate, BitInput.ofAffine, Vector.get_ofFn]
  rfl

/-- The arithmetic selector equals the original selected-label definition. -/
theorem selectedLabelWord_source [BN254.FieldCertificate] (coin : OfflineCoin) (input : BN254.AffineInput)
    (base : Memory) (stored : WordsAt base.ram (base.registers 11) 0 (offlineSchedule.words coin))
    (coordinates : base.ram (base.registers 12) = BitVec.ofNat 256 input.x.val ∧
      base.ram (base.registers 12 + 1) = BitVec.ofNat 256 input.y.val) (index : Fin 508) :
    selectedLabelWord index base = ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).get index).setWidth 256 := by
  by_cases low : index.val < 254
  · let bit : Fin 254 := ⟨index.val, low⟩
    have keys := offline_x_key coin base.ram (base.registers 11) stored bit
    have mask : selectedBitWord index base = if (coordinateBits input.x).getLsb bit then 1 else 0 := by
      simp only [selectedBitWord, selectedCoordinate, selectedBit, if_pos low, BitVec.add_zero, coordinates.1]
      exact (selected_bit_mask _ index.val).trans (congrArg (fun value : Bool => if value then (1 : Word) else 0) (coordinate_word_bit input.x bit))
    have prior : BitVec.ofNat 256 (510 + 2 * index.val) - 1#256 = BitVec.ofNat 256 (509 + 2 * index.val) := by
      rw [show 510 + 2 * index.val = (509 + 2 * index.val) + 1 by omega, BitVec.ofNat_add]
      simp
    rw [selectedLabelWord, mask, selectedLabels_low _ _ index low]
    change base.ram (base.registers 11 + (BitVec.ofNat 256 (selectedFalseOffset index) -
      (if (coordinateBits input.x).getLsb bit then 1 else 0))) =
      (BitAdaptor.encode (coin.2.1.x.get bit) ((coordinateBits input.x).getLsb bit)).setWidth 256
    cases chosen : (coordinateBits input.x).getLsb bit <;>
      simp [selectedFalseOffset, low, prior, keys.1, keys.2, BitAdaptor.encode, bit]
  · let bit : Fin 254 := ⟨index.val - 254, by change index.val - 254 < 254; have bound := index.isLt; omega⟩
    have keys := offline_y_key coin base.ram (base.registers 11) stored bit
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
      (BitAdaptor.encode (coin.2.1.y.get bit) ((coordinateBits input.y).getLsb bit)).setWidth 256
    cases chosen : (coordinateBits input.y).getLsb bit <;>
      simp [selectedFalseOffset, low, prior, keys.1, keys.2, BitAdaptor.encode, bit]

end Kriterion.ArgoMAC.ArithmeticSimulator
