import Proof.Privacy.Simulator.Arithmetic.RecordedPublicNonfixed

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle

/-- An accepted overlaid forward reply has one canonical 128-bit value. -/
theorem programmedForwardSamples_valueWitness [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * (state.base.used + 1) ≤ 2 ^ 110)
    (overlayRoom : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.base.used memory).support)
    (accepted : final.registers 7 ≠ 0#256) :
    ∃ value : Fin (2 ^ 128), (overlayForwardScan state.overlay.length final).1.registers 8 = BitVec.ofNat 256 value.val := by
  have reached : some ((overlayForwardScan state.overlay.length final).1.registers 8) ∈
      ((storedForwardSamples attempts state.base.used memory).map
        (fun result => overlayQueryValue state.overlay.length result.1)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, by simp [overlayQueryValue, accepted]⟩
  rw [programmedForwardSamples_wordReply attempts memory oracle state input represented index operand room overlayRoom] at reached
  obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases value with
  | none => simp at same
  | some value => exact ⟨value.1, (Option.some.inj same).symm⟩

/-- An accepted inverse reply has one canonical 128-bit value. -/
theorem programmedInverseSamples_valueWitness [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * state.base.used ≤ 2 ^ 110)
    (overlayRoom : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts state.base.used
      (publicInversePrepared state.overlay.length memory)).support)
    (accepted : final.registers 7 ≠ 0#256) :
    ∃ value : Fin (2 ^ 128), final.registers 8 = BitVec.ofNat 256 value.val := by
  have reached : some (final.registers 8) ∈
      ((storedInverseSamples attempts state.base.used (publicInversePrepared state.overlay.length memory)).map
        (fun result => queryValue result.1)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, by simp [queryValue, accepted]⟩
  rw [programmedInverseSamples_wordReply attempts memory oracle state input represented index operand room overlayRoom] at reached
  obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases value with
  | none => simp at same
  | some value => exact ⟨value.1, (Option.some.inj same).symm⟩

/-- The typed block parser preserves a canonical full-word reply. -/
theorem historyWord_parsed (value : Fin (2 ^ 128)) :
    historyWord (BitVec.ofNat 128 (BitVec.ofNat 256 value.val).toNat) = BitVec.ofNat 256 value.val := by
  have bound : value.val < 2 ^ 256 := lt_trans value.isLt (by decide)
  simp only [historyWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.mod_eq_of_lt value.isLt]

end Kriterion.ArgoMAC.ArithmeticSimulator
