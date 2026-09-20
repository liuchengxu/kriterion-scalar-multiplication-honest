import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrefix
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineSetup
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelStoreFrame
import Proof.Privacy.Simulator.Arithmetic.RetargetCurveFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each input-record cell is outside the original-label buffer. -/
theorem onlineInput_labelSeparate (offset : Fin 5) (index : Fin 508) :
    BitVec.ofNat 256 (onlineInputBase + offset.val) ≠
      BitVec.ofNat 256 onlineOriginalBase + BitVec.ofNat 256 index.val := by
  have firstFits : onlineInputBase + offset.val < 2 ^ 256 := by
    have bound := offset.isLt
    have numeric : onlineInputBase + 5 < 2 ^ 256 := by decide
    omega
  have secondFits : onlineOriginalBase + index.val < 2 ^ 256 := by
    have bound := index.isLt
    have numeric : onlineOriginalBase + 508 < 2 ^ 256 := by decide
    omega
  intro same
  rw [← BitVec.ofNat_add] at same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt secondFits] at values
  have bound := offset.isLt
  unfold onlineInputBase onlineOriginalBase at values
  omega

/-- Each input-record cell is outside the curve low-target update. -/
theorem onlineInput_curveSeparate (offset : Fin 5) :
    BitVec.ofNat 256 (onlineInputBase + offset.val) ≠ BitVec.ofNat 256 privateBase + 834903 := by
  have firstFits : onlineInputBase + offset.val < 2 ^ 256 := by
    have bound := offset.isLt
    have numeric : onlineInputBase + 5 < 2 ^ 256 := by decide
    omega
  have secondFits : privateBase + 834903 < 2 ^ 256 := by decide
  intro same
  change BitVec.ofNat 256 (onlineInputBase + offset.val) =
    BitVec.ofNat 256 privateBase + BitVec.ofNat 256 834903 at same
  rw [← BitVec.ofNat_add] at same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt firstFits, Nat.mod_eq_of_lt secondFits] at values
  unfold onlineInputBase at values
  omega

/-- The common curve prefix preserves all five parsed input words. -/
theorem onlineCurveMemory_input [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) (offset : Fin 5) :
    (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + offset.val)) =
      (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + offset.val)) := by
  let read := onlineReadMemory memory input output rest
  let prepared := executeLinear onlineOriginalSetup read
  have setup := onlineOriginalSetup_state read
  have pointer : (onlineOriginalMemory memory input output rest).registers 11 = BitVec.ofNat 256 privateBase := by
    exact (selectedLabelStoreCode_caller prepared 11 (by decide)).trans setup.2.2.1
  rw [onlineCurveMemory, retargetCurveCode_outside]
  · change (executeLinear selectedLabelStoreCode prepared).ram _ = _
    rw [selectedLabelStoreCode_outside]
    · exact congrFun setup.1 _
    · intro index
      rw [show prepared.registers 14 = BitVec.ofNat 256 onlineOriginalBase from setup.2.2.2.2]
      exact onlineInput_labelSeparate offset index
  · rw [pointer]
    exact onlineInput_curveSeparate offset

/-- The reader stores the exact output tag in the fixed input record. -/
theorem onlineReadMemory_tag [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) :
    (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + 2)) =
      BitVec.ofNat 256 (onlineOutputWords output).1 := by
  rw [onlineReadMemory, (onlineInputMemory_values (onlineInputPrepared memory) input output rest).1]
  have pointer : (onlineInputPrepared memory).registers 10 = BitVec.ofNat 256 onlineInputBase := rfl
  simp only [onlineRecordRam, pointer]
  have position : BitVec.ofNat 256 (onlineInputBase + 2) = BitVec.ofNat 256 onlineInputBase + 2 := by
    rw [BitVec.ofNat_add]
    rfl
  rw [position]
  have other4 : BitVec.ofNat 256 onlineInputBase + (2 : Word) ≠ BitVec.ofNat 256 onlineInputBase + 4 := by
    exact fun same => (by decide : (2 : Word) ≠ 4) (add_left_cancel same)
  have other3 : BitVec.ofNat 256 onlineInputBase + (2 : Word) ≠ BitVec.ofNat 256 onlineInputBase + 3 := by
    exact fun same => (by decide : (2 : Word) ≠ 3) (add_left_cancel same)
  rw [Function.update_of_ne other4, Function.update_of_ne other3, Function.update_self]


/-- The common prefix retains the exact validity tag for its first branch. -/
theorem onlineCurveMemory_tag [BN254.FieldCertificate] (memory : Memory) (input : BN254.AffineInput)
    (output : Option BN254.Point) (rest : List Bool) :
    (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 (onlineInputBase + 2)) =
      BitVec.ofNat 256 (onlineOutputWords output).1 :=
  (onlineCurveMemory_input memory input output rest 2).trans (onlineReadMemory_tag memory input output rest)

end Kriterion.ArgoMAC.ArithmeticSimulator
