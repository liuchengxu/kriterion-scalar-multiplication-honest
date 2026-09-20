import Proof.Privacy.Simulator.Arithmetic.OnlinePrefixBits
import Proof.Privacy.Simulator.Arithmetic.GateLoopBits
import Proof.Privacy.Simulator.Arithmetic.EncLinkBits
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineValid
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsMemory
import Proof.Privacy.Simulator.Arithmetic.RetargetPointFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples retargetPointCode

/-- The point-loop entry preserves all bit stacks. -/
theorem onlinePointGateInitial_bits (memory : Memory) :
    (onlinePointGateInitial memory).bits = memory.bits :=
  (onlinePointSetup_state (onlineTagMemory memory)).2.1

/-- An aborted point branch preserves all bit stacks. -/
theorem onlinePointBranchSamples_abortBits [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlinePointBranchSamples attempts memory).support)
    (aborted : result.1.pc ≠ 290305298) : result.1.memory.bits = memory.bits := by
  obtain ⟨outer, outerMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨point, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp outerMember
  have kept := gateLoopSamples_bits pointGatePlan attempts 277368 0 _ point member
  cases success : point.1 with
  | true => exact False.elim (aborted (by simp [onlinePointGateResult, success]))
  | false =>
      simp only [onlinePointGateResult, success, Bool.false_eq_true, ↓reduceIte] at ⊢
      exact kept.trans (onlinePointGateInitial_bits memory)

/-- An aborted complete gate phase preserves all bit stacks. -/
theorem onlineGateSamples_abortBits [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlineGateSamples attempts memory).support)
    (aborted : result.1.pc ≠ 290305298) : result.1.memory.bits = memory.bits := by
  obtain ⟨body, bodyMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨curve, member, later⟩ := (PMF.mem_support_bind_iff _ _ _).mp bodyMember
  obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp later
  have kept := (gateLoopSamples_bits curveGatePlan attempts 1270 0 _ curve member).trans
    (onlineOriginalSetup_state memory).2.1
  unfold onlineAfterCurveSamples at lastMember
  split at lastMember
  · exact (onlinePointBranchSamples_abortBits attempts curve.2.1 last lastMember aborted).trans kept
  · have same := (PMF.mem_support_pure_iff _ _).mp lastMember
    subst last
    exact kept

/-- An aborted link and gate phase preserves the output bit stack. -/
theorem onlineLinkSamples_abortBits3 [BN254.FieldCertificate] (attempts : Nat)
    (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlineLinkSamples attempts memory state key suffix).support)
    (aborted : result.1.pc ≠ 290305298) : result.1.memory.bits 3 = memory.bits 3 := by
  obtain ⟨link, member, later⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp later
  have kept := encLinkSamples_bits3 attempts memory state key suffix link member
  unfold onlineAfterLinkSamples at lastMember
  split at lastMember
  · exact (congrFun (onlineGateSamples_abortBits attempts link.1.1 last lastMember aborted) 3).trans kept
  · have same := (PMF.mem_support_pure_iff _ _).mp lastMember
    subst last
    exact kept

/-- The selected-target and retarget preparation preserves all bit stacks. -/
theorem onlinePreparedMemory_bits [BN254.FieldCertificate] [BN254.GroupCertificate]
    (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (onlinePreparedMemory memory output sample).bits = memory.bits := by
  unfold onlinePreparedMemory onlineTargetMemory
  rw [(onlineLinkSetup_state _).2.1, (retargetPointCode_preserves _).1,
    (onlineRetargetSetup_state _).2.1, outputTargetsMemory_bits, (onlineTargetSetup_state _).2.1]

/-- An aborted sampled body preserves the output bit stack. -/
theorem onlineValidBodySamples_abortBits3 [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point) (state : SparseOracleFamily)
    (key : BN254.BaseField) (suffix : List Bool) (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlineValidBodySamples attempts memory output state key suffix).support)
    (aborted : result.1.pc ≠ 290305298) : result.1.memory.bits 3 = memory.bits 3 := by
  obtain ⟨body, bodyMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨sample, member, later⟩ := (PMF.mem_support_bind_iff _ _ _).mp bodyMember
  obtain ⟨prepared, preparedMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp later
  obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp preparedMember
  have kept := onlineLinkSamples_abortBits3 attempts _ state key suffix last lastMember aborted
  rw [onlinePreparedMemory_bits, onlineSamplingMemory_bits attempts _ sample.1 sample.2 member] at kept
  exact kept

/-- An aborted complete valid response retains its initial output bit stack. -/
theorem onlineValidSamples_abortBits3 [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (input : BN254.AffineInput) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlineValidSamples attempts memory input output state key suffix).support)
    (aborted : result.1.pc ≠ 290305298) : result.1.memory.bits 3 = memory.bits 3 := by
  obtain ⟨branch, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨body, bodyMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have kept := onlineValidBodySamples_abortBits3 attempts _ output state key suffix body bodyMember aborted
  change body.1.memory.bits 3 = _
  rw [kept]
  change (onlineCurveMemory memory input (some output) suffix).bits 3 = memory.bits 3
  rw [onlineCurveMemory_bits]
  rfl

/-- The parser rejects every aborted valid response with an empty initial output stack. -/
theorem onlineValidSamples_abortParser [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (input : BN254.AffineInput) (output : BN254.Point)
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (empty : memory.bits 3 = []) (result : Configuration 290305300 × Nat)
    (supported : result ∈ (onlineValidSamples attempts memory input output state key suffix).support)
    (aborted : result.1.pc ≠ 290305298) :
    GarbledCircuit.SimulatorProtocol.words 128 508 (result.1.memory.bits 3) = none := by
  rw [onlineValidSamples_abortBits3 attempts memory input output state key suffix result supported aborted, empty]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
