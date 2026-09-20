import Proof.Privacy.Simulator.Arithmetic.OnlineMachineInputFrame
import Proof.Privacy.Simulator.Arithmetic.PublicLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling
noncomputable section

private theorem earlierWord_ne (cell base offset : Nat) (lower : cell < base) (fits : base + offset < 2 ^ 256) :
    BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 base + BitVec.ofNat 256 offset := by
  intro same
  rw [← BitVec.ofNat_add] at same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cell < 2 ^ 256), Nat.mod_eq_of_lt fits] at values
  omega

/-- The input reader preserves every cell before its five-word input record. -/
theorem onlineReadMemory_before [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (cell : Nat) (lower : cell < onlineInputBase) :
    (onlineReadMemory memory input output rest).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [onlineReadMemory, (onlineInputMemory_values (onlineInputPrepared memory) input output rest).1]
  have pointer : (onlineInputPrepared memory).registers 10 = BitVec.ofNat 256 onlineInputBase := rfl
  have different (offset : Fin 5) :
      BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 offset.val := by
    apply earlierWord_ne cell onlineInputBase offset.val lower
    have bound := offset.isLt
    have room : onlineInputBase + 5 < 2 ^ 256 := by decide
    omega
  simp only [onlineRecordRam, pointer]
  rw [Function.update_of_ne (show BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 onlineInputBase + (4 : Word) from different 4),
    Function.update_of_ne (show BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 onlineInputBase + (3 : Word) from different 3),
    Function.update_of_ne (show BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 onlineInputBase + (2 : Word) from different 2),
    Function.update_of_ne (show BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 onlineInputBase + (1 : Word) from different 1),
    Function.update_of_ne (by simpa using different 0)]
  rfl

/-- The common curve prefix preserves the bridge key, labels, and all point-row source words. -/
theorem onlineCurveMemory_before [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (cell : Nat) (lower : cell < privateBase + 834395) :
    (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  let read := onlineReadMemory memory input output rest
  let prepared := executeLinear onlineOriginalSetup read
  have setup := onlineOriginalSetup_state read
  have pointer : (onlineOriginalMemory memory input output rest).registers 11 = BitVec.ofNat 256 privateBase :=
    (selectedLabelStoreCode_caller prepared 11 (by decide)).trans setup.2.2.1
  rw [onlineCurveMemory, retargetCurveCode_outside]
  · change (executeLinear selectedLabelStoreCode prepared).ram _ = _
    rw [selectedLabelStoreCode_outside]
    · rw [show prepared.ram = read.ram from setup.1]
      exact onlineReadMemory_before memory input output rest cell (lt_of_lt_of_le lower (by decide))
    · intro index
      rw [show prepared.registers 14 = BitVec.ofNat 256 onlineOriginalBase from setup.2.2.2.2]
      apply earlierWord_ne cell onlineOriginalBase index.val
      · exact lt_of_lt_of_le lower (by decide)
      · have bound := index.isLt
        have room : onlineOriginalBase + 508 < 2 ^ 256 := by decide
        omega
  · rw [pointer]
    intro same
    change BitVec.ofNat 256 cell = BitVec.ofNat 256 privateBase + BitVec.ofNat 256 834903 at same
    rw [← BitVec.ofNat_add] at same
    exact (earlierWord_ne cell (privateBase + 834903) 0
      (lt_of_lt_of_le lower (by decide)) (by decide)) (by simpa using same)

/-- The reached curve-prefix memory retains every original typed point row. -/
theorem onlineCurveMemory_pointRows [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    ∀ row : Fin FieldMacToECMac.outputMacCount, WordsAt (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 privateBase)
      (1017 + 9158 * row.val) (rowSchedule.words (coin.1.points.get row)) := by
  intro row index inside
  have original := public_row_words coin.1 memory.ram (BitVec.ofNat 256 privateBase) row
    (offline_public_words coin memory.ram _ stored)
  rw [← BitVec.ofNat_add, onlineCurveMemory_before]
  · simpa only [BitVec.ofNat_add] using original index inside
  · rw [rowSchedule.wordsLength] at inside
    have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
    have bound := row.isLt
    omega

end
end Kriterion.ArgoMAC.ArithmeticSimulator
