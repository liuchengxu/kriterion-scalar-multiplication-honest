import Proof.Privacy.Simulator.Arithmetic.OnlineTargetBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling
noncomputable section

/-- The complete offline representation supplies every original point row. -/
theorem offlineWords_pointRows (memory : Memory) (coin : OfflineCoin)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 privateBase) 0 (offlineSchedule.words coin)) :
    ∀ row : Fin FieldMacToECMac.outputMacCount, WordsAt memory.ram (BitVec.ofNat 256 privateBase)
      (1017 + 9158 * row.val) (rowSchedule.words (coin.1.points.get row)) := by
  intro row
  exact public_row_words coin.1 memory.ram _ row (offline_public_words coin memory.ram _ stored)

/-- Each selected target lies outside every original point-row write. -/
theorem onlineTarget_pointSeparate (source written : Fin FieldMacToECMac.outputMacCount) (coordinate : Fin 3) :
    OutsidePointRow (BitVec.ofNat 256 privateBase) written
      (BitVec.ofNat 256 onlineTargetBase + BitVec.ofNat 256 (3 * source.val + coordinate.val)) := by
  have sourceBound := source.isLt
  have writtenBound := written.isLt
  have coordinateBound := coordinate.isLt
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have targetOffset : onlineTargetBase = privateBase + 838574 := by decide
  rw [targetOffset, BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  refine ⟨?_, ?_, ?_⟩
  · apply privateOffset_add_ne _ _ _ 762 <;> omega
  · apply privateOffset_add_ne _ _ _ 508 <;> omega
  · apply privateOffset_add_ne _ _ _ 1016 <;> omega

/-- The actual sampler and target writer preserve all source and input words below the sample region. -/
theorem onlineRetargetSetup_before [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (cell : Nat) (lower : cell < onlineSampleBase) :
    (executeLinear onlineRetargetSetup (onlineTargetMemory final output sample)).ram (BitVec.ofNat 256 cell) =
      memory.ram (BitVec.ofNat 256 cell) := by
  rw [(onlineRetargetSetup_state _).1, onlineTargetMemory_before]
  · exact onlineSamplingMemory_before attempts memory final cost cell pointer supported lower
  · have layout := onlineBuffer_bounds.2.2.2.1
    omega

/-- The reached retarget entry supplies the original rows, input, targets, and disjoint target addresses. -/
theorem onlineRetargetSetup_ready [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (input : AffineInput) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (rows : Fin FieldMacToECMac.outputMacCount → RowPublicSample)
    (stored : ∀ row, WordsAt memory.ram (BitVec.ofNat 256 privateBase)
      (1017 + 9158 * row.val) (rowSchedule.words (rows row)))
    (coordinates : memory.ram (BitVec.ofNat 256 onlineInputBase) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (BitVec.ofNat 256 onlineInputBase + 1) = BitVec.ofNat 256 input.y.val) :
    let prepared := executeLinear onlineRetargetSetup (onlineTargetMemory final output sample)
    (∀ row, WordsAt prepared.ram (prepared.registers 11)
      (1017 + 9158 * row.val) (rowSchedule.words (rows row))) ∧
    (prepared.ram (prepared.registers 12) = BitVec.ofNat 256 input.x.val ∧
      prepared.ram (prepared.registers 12 + 1) = BitVec.ofNat 256 input.y.val) ∧
    (∀ row coordinate, prepared.ram (prepared.registers 14 + BitVec.ofNat 256 (3 * row.val + coordinate.val)) =
      BitVec.ofNat 256 (onlineTargetField output sample row coordinate).val) ∧
    (∀ (source written : Fin FieldMacToECMac.outputMacCount) (coordinate : Fin 3), OutsidePointRow (prepared.registers 11) written
      (prepared.registers 14 + BitVec.ofNat 256 (3 * source.val + coordinate.val))) := by
  dsimp only
  have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
  have setup := onlineRetargetSetup_state (onlineTargetMemory final output sample)
  have frame := onlineRetargetSetup_before attempts memory final cost pointer supported output sample
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro row index inside
    rw [setup.2.2.1, ← BitVec.ofNat_add, frame]
    · simpa only [BitVec.ofNat_add] using stored row index inside
    · rw [rowSchedule.wordsLength] at inside
      have rowBound := row.isLt
      change privateBase + (1017 + 9158 * row.val + index) < onlineSampleBase
      unfold onlineSampleBase
      omega
  · rw [setup.2.2.2.1]
    constructor
    · rw [frame onlineInputBase (by decide)]
      exact coordinates.1
    · have address : BitVec.ofNat 256 onlineInputBase + 1 = BitVec.ofNat 256 (onlineInputBase + 1) := by
        rw [BitVec.ofNat_add]; rfl
      rw [address, frame (onlineInputBase + 1) (by decide), ← address]
      exact coordinates.2
  · intro row coordinate
    rw [setup.1, setup.2.2.2.2]
    exact onlineTargetMemory_field final output sample row coordinate
  · intro source written coordinate
    rw [setup.2.2.1, setup.2.2.2.2]
    exact onlineTarget_pointSeparate source written coordinate

end
end Kriterion.ArgoMAC.ArithmeticSimulator
