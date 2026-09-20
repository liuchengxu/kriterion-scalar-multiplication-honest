import Proof.Privacy.Simulator.Arithmetic.OnlineSelectedBounds
import Proof.Privacy.Simulator.Arithmetic.GateCodeTyped

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
attribute [local irreducible] selectedLabelStoreCode selectedLabelStoreProgram

/-- The original-label store writes the exact selected key labels. -/
theorem onlineOriginalMemory_label [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) (index : Fin 508) :
    (onlineOriginalMemory memory input output rest).ram
      (BitVec.ofNat 256 onlineOriginalBase + BitVec.ofNat 256 index.val) =
      ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).get index).setWidth 256 := by
  let prepared := executeLinear onlineOriginalSetup (onlineReadMemory memory input output rest)
  have setup := onlineOriginalSetup_state (onlineReadMemory memory input output rest)
  have source : WordsAt prepared.ram (prepared.registers 11) 0 (offlineSchedule.words coin) := by
    rw [setup.1, setup.2.2.1]
    intro offset inside
    rw [← BitVec.ofNat_add, onlineReadMemory_before]
    · simpa only [BitVec.ofNat_add] using stored offset inside
    · rw [offlineSchedule.wordsLength] at inside
      unfold onlineInputBase
      omega
  have coordinates : prepared.ram (prepared.registers 12) = BitVec.ofNat 256 input.x.val ∧
      prepared.ram (prepared.registers 12 + 1) = BitVec.ofNat 256 input.y.val := by
    rw [setup.1, setup.2.2.2.1]
    exact onlineReadMemory_coordinates memory input output rest
  have value := selectedLabelStoreProgram_source coin input prepared source coordinates
    (onlineOriginal_disjoint prepared setup.2.2.1 setup.2.2.2.1 setup.2.2.2.2) index
  change (executeLinear selectedLabelStoreCode prepared).ram _ = _
  rw [selectedLabelStoreCode_eq]
  have pointer : prepared.registers 14 = BitVec.ofNat 256 onlineOriginalBase := setup.2.2.2.2
  rw [pointer] at value
  exact value

/-- The curve update preserves each selected original label. -/
theorem onlineCurveMemory_label [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) (index : Fin 508) :
    (onlineCurveMemory memory input output rest).ram
      (BitVec.ofNat 256 onlineOriginalBase + BitVec.ofNat 256 index.val) =
      ((Lamport.selectedLabels (coin.2.1.encodeAffine input)).get index).setWidth 256 := by
  rw [onlineCurveMemory_ram memory input output rest coin stored, Function.update_of_ne]
  · exact onlineOriginalMemory_label memory input output rest coin stored index
  · change BitVec.ofNat 256 onlineOriginalBase + BitVec.ofNat 256 index.val ≠
      BitVec.ofNat 256 privateBase + BitVec.ofNat 256 834903
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    intro same
    have bound := index.isLt
    have fits : onlineOriginalBase + index.val < 2 ^ 256 := by
      have fixed : onlineOriginalBase + 508 < 2 ^ 256 := by decide
      omega
    have values := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
      Nat.mod_eq_of_lt (by decide : privateBase + 834903 < 2 ^ 256)] at values
    unfold onlineOriginalBase at values
    omega

/-- The signature vector has the same flat order as the input MAC. -/
theorem encLinkMacWords_selected (mac : InputMac) :
    encLinkMacWords mac = (Lamport.selectedLabels mac).toList := by
  apply List.ext_getElem
  · simp [encLinkMacWords, coordinateBitCount]
  · intro index first second
    by_cases low : index < 254
    · simp [encLinkMacWords, List.getElem_append, low, Lamport.selectedLabels, Vector.get, coordinateBitCount]
    · simp [encLinkMacWords, List.getElem_append, low, Lamport.selectedLabels, Vector.get, coordinateBitCount]

/-- The common curve prefix stores the complete widened selected-label array. -/
theorem onlineCurveMemory_labels [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    WordsAt (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 onlineOriginalBase) 0
      ((encLinkMacWords (coin.2.1.encodeAffine input)).map (fun label => label.setWidth 256)) := by
  rw [encLinkMacWords_selected]
  intro index inside
  have valid : index < 508 := by simpa using inside
  simpa [Vector.get] using onlineCurveMemory_label memory input output rest coin stored ⟨index, valid⟩

/-- The curve prefix retains the original key array for final output. -/
theorem onlineCurveMemory_keys [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    WordsAt (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 privateBase) 1
      (inputKeySchedule.words coin.2.1) := by
  have keys := offline_inputKey_words coin memory.ram _ stored
  intro index inside
  rw [← BitVec.ofNat_add, onlineCurveMemory_before]
  · simpa only [BitVec.ofNat_add] using keys index inside
  · rw [inputKeySchedule.wordsLength] at inside
    omega

/-- The curve prefix retains both fixed input-coordinate words. -/
theorem onlineCurveMemory_coordinates [FieldCertificate] (memory : Memory) (input : AffineInput)
    (output : Option Point) (rest : List Bool) :
    (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    (onlineCurveMemory memory input output rest).ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val := by
  have values := onlineReadMemory_coordinates memory input output rest
  have x := onlineCurveMemory_input memory input output rest 0
  have y := onlineCurveMemory_input memory input output rest 1
  simpa only [Fin.val_zero, Nat.add_zero, Fin.val_one, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using
    And.intro (x.trans values.1) (y.trans values.2)

end Kriterion.ArgoMAC.ArithmeticSimulator
