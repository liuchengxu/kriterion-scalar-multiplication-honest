import Proof.Privacy.Simulator.Arithmetic.OnlineCurveLabels
import Proof.Privacy.Simulator.Arithmetic.OnlineRetargetBuffers
import Proof.Privacy.Simulator.Arithmetic.SelectedLabelsKeyProtocol
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
noncomputable section

/-- The valid private preparation preserves the keys, curve data, and input record. -/
theorem onlinePreparedMemory_outsidePoints [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (offset : Nat) (outside : offset < 1017 ∨ 834395 ≤ offset) (bound : offset < 838213) :
    (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 privateBase + BitVec.ofNat 256 offset) =
      memory.ram (BitVec.ofNat 256 privateBase + BitVec.ofNat 256 offset) := by
  rw [onlinePreparedMemory, (onlineLinkSetup_state _).1, retargetPointCode_outside]
  · rw [← BitVec.ofNat_add]
    exact onlineRetargetSetup_before attempts memory final cost pointer supported output sample
      (privateBase + offset) (by unfold onlineSampleBase; omega)
  · intro row
    rw [(onlineRetargetSetup_state _).2.2.1]
    have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
    have rowBound := row.isLt
    refine ⟨?_, ?_, ?_⟩
    · apply privateOffset_add_ne _ _ _ 762 <;> omega
    · apply privateOffset_add_ne _ _ _ 508 <;> omega
    · apply privateOffset_add_ne _ _ _ 1016 <;> omega

/-- The valid private preparation retains every original input-key word. -/
theorem onlinePreparedMemory_keys [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) (key : InputMacKey)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words key)) :
    WordsAt (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 privateBase) 1
      (inputKeySchedule.words key) := by
  intro index inside
  have bound : index < 1016 := by simpa only [inputKeySchedule.wordsLength] using inside
  rw [onlinePreparedMemory_outsidePoints attempts memory final cost pointer supported output sample
    (1 + index) (Or.inl (by omega)) (by omega)]
  exact stored index inside

/-- The valid private preparation retains both fixed input-coordinate words. -/
theorem onlinePreparedMemory_coordinates [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (input : AffineInput) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val) :
    (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
    (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val := by
  have x := onlinePreparedMemory_outsidePoints attempts memory final cost pointer supported output sample
    838208 (Or.inr (by decide)) (by decide)
  have y := onlinePreparedMemory_outsidePoints attempts memory final cost pointer supported output sample
    838209 (Or.inr (by decide)) (by decide)
  have xAddress : BitVec.ofNat 256 privateBase + BitVec.ofNat 256 838208 = BitVec.ofNat 256 onlineInputBase := by
    rw [← BitVec.ofNat_add]; rfl
  have yAddress : BitVec.ofNat 256 privateBase + BitVec.ofNat 256 838209 = BitVec.ofNat 256 onlineInputBase + 1 := by
    rw [← BitVec.ofNat_add]
    rfl
  rw [xAddress] at x
  rw [yAddress] at y
  exact ⟨x.trans coordinates.1, y.trans coordinates.2⟩

/-- The final emitter preserves every source word. -/
theorem onlineFinalMemory_ram (memory : Memory) : (onlineFinalMemory memory).ram = memory.ram := by
  rw [onlineFinalMemory, selectedLabelsCode_eq, (selectedLabelsProgram_preserves _).1,
    (onlineLabelSetup_state memory).1]

/-- The final emitter returns the exact original signature from its retained key buffer. -/
theorem onlineFinalMemory_keyProtocol [FieldCertificate] (memory : Memory) (key : InputMacKey) (input : AffineInput)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 1 (inputKeySchedule.words key))
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val)
    (empty : memory.bits 3 = []) :
    GarbledCircuit.SimulatorProtocol.words 128 508 ((onlineFinalMemory memory).bits 3) =
      some (Lamport.selectedLabels (key.encodeAffine input)) := by
  have setup := onlineLabelSetup_state memory
  have keys : WordsAt (executeLinear onlineLabelSetup memory).ram
      ((executeLinear onlineLabelSetup memory).registers 11) 1 (inputKeySchedule.words key) := by
    rw [setup.1, setup.2.2.1]
    exact stored
  have data : (executeLinear onlineLabelSetup memory).ram ((executeLinear onlineLabelSetup memory).registers 12) =
      BitVec.ofNat 256 input.x.val ∧
      (executeLinear onlineLabelSetup memory).ram ((executeLinear onlineLabelSetup memory).registers 12 + 1) =
        BitVec.ofNat 256 input.y.val := by
    rw [setup.1, setup.2.2.2]
    exact coordinates
  rw [onlineFinalMemory, selectedLabelsCode_keyBits key input _ keys data,
    Function.update_self, setup.2.1, empty, List.append_nil]
  exact words_encoded 128 508 (Lamport.selectedLabels (key.encodeAffine input))

end
end Kriterion.ArgoMAC.ArithmeticSimulator
