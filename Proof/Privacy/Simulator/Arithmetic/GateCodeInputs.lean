import Proof.Privacy.Simulator.Arithmetic.GateDriverPrepared
import Proof.Privacy.Simulator.Arithmetic.GateSchedule
import Proof.Privacy.Simulator.Arithmetic.EncLinkProgramRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security

/-- Each descriptor reads the same coordinate bit as its typed directive. -/
theorem gateCodeAt_bit (location : Pipeline.FixedKeyLocation) (isX : Bool)
    (start gates gate : Nat) (bit : Fin 254) (memory : Memory) (input : AffineInput)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val) :
    gateDriverBit (gateCodeAt location isX start gates gate bit) memory =
      if isX then coordinateValues input.x bit else coordinateValues input.y bit := by
  have bound := bit.isLt
  cases isX
  · have high : ¬254 + bit.val < 254 := by omega
    simp only [gateDriverBit, gateCodeAt, Bool.false_eq_true, ↓reduceIte, selectedCoordinate,
      selectedBit, high, Nat.add_sub_cancel_left]
    have yword : memory.ram (memory.registers 12 + 1#256) = BitVec.ofNat 256 input.y.val := coordinates.2
    rw [yword]
    exact coordinate_word_bit input.y bit
  · simp only [gateDriverBit, gateCodeAt, ↓reduceIte, Nat.zero_add, selectedCoordinate,
      selectedBit, bound, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rw [coordinates.1]
    exact coordinate_word_bit input.x bit

/-- The flat label array stores each X label before every Y label. -/
theorem encLinkMacWords_x (mac : InputMac) (bit : Fin 254) :
    (encLinkMacWords mac)[bit.val]'(by simp only [encLinkMacWords, List.length_map, List.length_append, Vector.length_toList, coordinateBitCount]; omega) = mac.x.get bit := by
  change (mac.x.toList ++ mac.y.toList)[bit.val] = _
  rw [List.getElem_append_left (by simpa using bit.isLt)]
  rfl

/-- The second half of the flat label array stores each Y label. -/
theorem encLinkMacWords_y (mac : InputMac) (bit : Fin 254) :
    (encLinkMacWords mac)[254 + bit.val]'(by simp only [encLinkMacWords, List.length_map, List.length_append, Vector.length_toList, coordinateBitCount]; omega) = mac.y.get bit := by
  change (mac.x.toList ++ mac.y.toList)[254 + bit.val] = _
  rw [List.getElem_append_right (by simp)]
  simp only [Vector.length_toList, Nat.add_sub_cancel_left]
  rfl

/-- Each descriptor loads the same widened label as its typed directive. -/
theorem gateCodeAt_label (location : Pipeline.FixedKeyLocation) (isX : Bool)
    (start gates gate : Nat) (bit : Fin 254) (memory : Memory) (mac : InputMac)
    (stored : WordsAt memory.ram (memory.registers 14) 0
      ((encLinkMacWords mac).map (fun label => label.setWidth 256))) :
    memory.ram (memory.registers 14 + BitVec.ofNat 256 (gateCodeAt location isX start gates gate bit).selected.val) =
      (if isX then mac.x.get bit else mac.y.get bit).setWidth 256 := by
  cases isX
  · have value := stored (254 + bit.val) (by simp only [encLinkMacWords, List.length_map, List.length_append, Vector.length_toList, coordinateBitCount]; omega)
    simpa only [gateCodeAt, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, List.getElem_map,
      encLinkMacWords_y] using value
  · have value := stored bit.val (by simp only [encLinkMacWords, List.length_map, List.length_append, Vector.length_toList, coordinateBitCount]; omega)
    simpa only [gateCodeAt, ↓reduceIte, Nat.zero_add, List.getElem_map, encLinkMacWords_x] using value

end Kriterion.ArgoMAC.ArithmeticSimulator
