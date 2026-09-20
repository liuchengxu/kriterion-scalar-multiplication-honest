import Proof.Privacy.Simulator.Arithmetic.OnlineKeyBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- A bounded word store preserves every later address. -/
theorem storeDrawWords_after (pointer cell : Nat) (ram : Word → Word) (words : List Word)
    (later : pointer + words.length ≤ cell) (fits : cell < 2 ^ 256) :
    storeDrawWords (BitVec.ofNat 256 pointer) 0 ram words (BitVec.ofNat 256 cell) =
      ram (BitVec.ofNat 256 cell) := by
  apply storeDrawWords_other
  intro index inside
  rw [Nat.zero_add, ← BitVec.ofNat_add]
  intro same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
    Nat.mod_eq_of_lt (by omega : pointer + index < 2 ^ 256)] at values
  omega

/-- The private sampler preserves the later original-label buffer. -/
theorem onlineSamplingMemory_after [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost cell : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (later : onlineOriginalBase ≤ cell) (fits : cell < 2 ^ 96) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨sample, _, stored⟩ := onlineSamplingMemory_witness attempts memory final cost supported
  rw [stored, pointer]
  apply storeDrawWords_after onlineSampleBase cell _ _ _ (lt_trans fits (by decide))
  rw [onlineWords_length]
  have separate : onlineSampleBase + 361 ≤ onlineOriginalBase := by decide
  exact separate.trans later

/-- The target writer preserves the later original-label buffer. -/
theorem onlineTargetMemory_after [FieldCertificate] [GroupCertificate]
    (memory : Memory) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (cell : Nat) (later : onlineOriginalBase ≤ cell) (fits : cell < 2 ^ 96) :
    (onlineTargetMemory memory output sample).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [onlineTargetMemory, outputTargetsMemory_ram, (onlineTargetSetup_state memory).1,
    (onlineTargetSetup_state memory).2.2.2.2.2]
  apply storeDrawWords_after onlineTargetBase cell _ _ _ (lt_trans fits (by decide))
  rw [← outputTargets_words, homogeneousRowsWords_length]
  have separate : onlineTargetBase + 273 = onlineOriginalBase := by decide
  exact separate.le.trans later

/-- The full private preparation preserves every original-label word. -/
theorem onlinePreparedMemory_after [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (cell : Nat) (later : onlineOriginalBase ≤ cell) (fits : cell < 2 ^ 96) :
    (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [onlinePreparedMemory, (onlineLinkSetup_state _).1, retargetPointCode_outside]
  · rw [(onlineRetargetSetup_state _).1, onlineTargetMemory_after final output sample cell later fits]
    exact onlineSamplingMemory_after attempts memory final cost cell pointer supported later fits
  · intro row
    rw [(onlineRetargetSetup_state _).2.2.1]
    have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
    have rowBound := row.isLt
    have apart (offset : Nat) (inside : offset < 838208) :
        BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 privateBase + BitVec.ofNat 256 offset := by
      rw [← BitVec.ofNat_add]
      intro same
      have values := congrArg BitVec.toNat same
      have bound : privateBase + offset < 2 ^ 256 := by
        have fixed : privateBase + 838208 < 2 ^ 256 := by decide
        omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans fits (by decide : 2 ^ 96 < 2 ^ 256)),
        Nat.mod_eq_of_lt bound] at values
      have separate : privateBase + 838208 < onlineOriginalBase := by decide
      omega
    have shifted (offset extra : Nat) (inside : offset + extra < 838208) :
        BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 privateBase + BitVec.ofNat 256 offset + BitVec.ofNat 256 extra := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact apart _ inside
    exact ⟨shifted (1017 + 9158 * row.val + 6105) 762 (by omega),
      shifted (1017 + 9158 * row.val + 3815) 508 (by omega),
      shifted (1017 + 9158 * row.val) 1016 (by omega)⟩

/-- The full private preparation retains the widened original-label array. -/
theorem onlinePreparedMemory_labels [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) (mac : InputMac)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 onlineOriginalBase) 0
      ((encLinkMacWords mac).map (fun label => label.setWidth 256))) :
    WordsAt (onlinePreparedMemory final output sample).ram (BitVec.ofNat 256 onlineOriginalBase) 0
      ((encLinkMacWords mac).map (fun label => label.setWidth 256)) := by
  intro index inside
  have bound : index < 508 := by simpa [encLinkMacWords, coordinateBitCount] using inside
  rw [← BitVec.ofNat_add, onlinePreparedMemory_after attempts memory final cost pointer supported output sample]
  · simpa only [BitVec.ofNat_add] using stored index inside
  · omega
  · have fixed : onlineOriginalBase + 508 < 2 ^ 96 := by decide
    omega

end Kriterion.ArgoMAC.ArithmeticSimulator
