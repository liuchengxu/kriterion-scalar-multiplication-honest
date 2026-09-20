import Proof.Privacy.Simulator.Arithmetic.OnlineCurvePublic
import Proof.Privacy.Simulator.Arithmetic.OnlineTargetBuffers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SharedSimulatorMachine

/-- The private preparation preserves every public oracle cell. -/
theorem onlinePreparedMemory_public [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (oracle : Fin 15749) (region : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (onlinePreparedMemory final output sample).ram (oracleAddress oracle region offset) =
      memory.ram (oracleAddress oracle region offset) := by
  rw [onlinePreparedMemory, (onlineLinkSetup_state _).1, retargetPointCode_outside]
  · rw [(onlineRetargetSetup_state _).1, onlineTargetMemory_public]
    · exact onlineSamplingMemory_public attempts memory final cost pointer supported oracle region offset fits
    · exact fits
  · intro row
    rw [(onlineRetargetSetup_state _).2.2.1]
    have rowBound := row.isLt
    have apart (cell : Nat) (small : cell < 2 ^ 96) :=
      oracleAddress_private_disjoint oracle region offset cell fits small
    refine ⟨?_, ?_, ?_⟩
    all_goals
      simp only [show (762 : Word) = BitVec.ofNat 256 762 from rfl,
        show (508 : Word) = BitVec.ofNat 256 508 from rfl,
        show (1016 : Word) = BitVec.ofNat 256 1016 from rfl]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      apply apart
      have rowCount : FieldMacToECMac.outputMacCount = 91 := rfl
      have maximum : privateBase + 834395 < 2 ^ 96 := by decide
      apply lt_trans _ maximum
      apply Nat.add_lt_add_left
      omega

/-- The private preparation retains the exact shared family and fixed histories. -/
theorem onlinePreparedMemory_shared [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (state : SharedOracleSource) (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) :
    SharedSourceMemory (onlinePreparedMemory final output sample) state limit := by
  have same := onlinePreparedMemory_public attempts memory final cost pointer supported output sample
  exact ⟨OracleFamilyMemory.congr _ _ state.family represented.family represented.capacity same,
    represented.capacity, SharedHistoryMemory.fixedFrame _ _ state.metadata state.metadata represented.history rfl
      (represented.historyFits room) (fun index offset fits => same _ 3 offset fits), represented.counts⟩

/-- The actual valid prefix and private preparation retain the initial shared source. -/
theorem onlineValidPrepared_shared [FieldCertificate] [GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (input : AffineInput) (output : Point)
    (state : SharedOracleSource) (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (sampled : Memory × Nat)
    (supported : sampled ∈ (onlineSamplingMemory attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) [])))).support) :
    let sample := onlineSamplingCoin attempts
      (onlineSampleInitial (onlineTagMemory (onlineCurveMemory memory input (some output) []))) sampled
    SharedSourceMemory (onlinePreparedMemory sampled.1 output sample) state limit := by
  have initialSource := onlineCurveMemory_shared memory input (some output) [] state limit represented room
  apply onlinePreparedMemory_shared attempts limit _ sampled.1 sampled.2 _ supported output _ state _ room
  · simp [onlineSampleInitial, onlineSampleSetup, executeLinear, LinearInstruction.execute]
  · exact initialSource.ramEq rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
