import Proof.Privacy.Simulator.SimulatorPrivacy

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions
namespace SimulatorMachine

/-- The original proof gives the full error envelope before it rounds the claim to 100 bits. -/
theorem compiled_small_error [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) (witness : Garbling.Randomness)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100) :
    advantage
      (GarbledCircuit.realGame (Garbling.garbledCircuit construction) (randomTape witness)
        Garbling.oracleHandler adversary parameter scalar auxiliary)
      (GarbledCircuit.idealGame (Garbling.garbledCircuit construction) Garbling.topology
        concreteCircuitSimulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) := by
  letI : Fintype Block := Fintype.ofFinite Block
  rw [adaptiveTranscriptWithState_advantage_eq]
  exact fullGateGhostRatio_event_bound adversary parameter auxiliary scalar witness
    (fullGateRealFallback adversary parameter auxiliary scalar witness)
    (fullGateRealFallback_length adversary parameter auxiliary scalar witness)
    (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
      (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary)
    (concreteSmallSourceRatio adversary parameter scalar auxiliary witness small) _

/-- The exact sparse three-phase game retains the original error envelope. -/
theorem operational_small_error [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    {Aux : Type} (adversary : ThreePhase.Adversary Aux) (parameter : Nat) (scalar : NonZeroScalar)
    (auxiliary : Aux) (witness : Garbling.Randomness)
    (small : adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
      adversary.decisionQueryBudget parameter < 2 ^ 100) :
    advantage (ThreePhase.realGame adversary parameter scalar auxiliary witness)
      (operationalIdealGame adversary parameter scalar auxiliary) ≤
      adaptiveErrorEnvelope (adversary.preQueryBudget parameter + adversary.inputQueryBudget parameter +
        adversary.decisionQueryBudget parameter) := by
  rw [operationalIdealGame_eq, ThreePhase.realGame_eq_compiled, ThreePhase.idealGame_eq_compiled]
  exact compiled_small_error adversary.compile parameter scalar auxiliary witness small

/-- This residual counts private samples, online samples, and all sparse oracle operations. -/
noncomputable def cutoffResidual (queries : Nat) : ℝ :=
  ((1813496 + queries : Nat) : ℝ) / (2 : ℝ) ^ 256

/-- The finite retry residual fits one inverse block per unit of adversary work. -/
theorem cutoffResidual_le (queries : Nat) :
    cutoffResidual queries ≤ ((queries + 1 : Nat) : ℝ) / (2 : ℝ) ^ 128 := by
  have countBound : 1813496 + queries ≤ (queries + 1) * 2 ^ 128 := by omega
  unfold cutoffResidual
  have castBound : ((1813496 + queries : Nat) : ℝ) ≤ ((queries + 1 : Nat) : ℝ) * 2 ^ 128 := by
    exact_mod_cast countBound
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256)).mpr
  calc
    _ ≤ ((queries + 1 : Nat) : ℝ) * 2 ^ 128 := castBound
    _ = _ := by norm_num [div_eq_mul_inv]; ring

/-- The complete finite retry error preserves the 100-bit work bound. -/
theorem cutoffEnvelope_has100Bits (queries : Nat) :
    WorkPerAdvantage 100 (queries + 1) (adaptiveErrorEnvelope queries + cutoffResidual queries) := by
  have countBound : adaptiveConstantCount + adaptiveQueryCount * queries + (queries + 1) ≤
      (queries + 1) * 2 ^ 28 := by
    change 227454970 + 824 * queries + (queries + 1) ≤ (queries + 1) * 268435456
    omega
  have castBound : ((adaptiveConstantCount + adaptiveQueryCount * queries + (queries + 1) : Nat) : ℝ) ≤
      ((queries + 1 : Nat) : ℝ) * 2 ^ 28 := by exact_mod_cast countBound
  unfold WorkPerAdvantage
  apply (mul_le_mul_of_nonneg_right
    (add_le_add_right (cutoffResidual_le queries) (adaptiveErrorEnvelope queries)) (by positivity)).trans
  change (adaptiveErrorEnvelope queries + ((queries + 1 : Nat) : ℝ) / 2 ^ 128) * 2 ^ 100 ≤ _
  have arithmetic : (adaptiveErrorEnvelope queries + ((queries + 1 : Nat) : ℝ) / 2 ^ 128) * 2 ^ 100 =
      ((adaptiveConstantCount + adaptiveQueryCount * queries + (queries + 1) : Nat) : ℝ) / 2 ^ 28 := by
    simp only [adaptiveErrorEnvelope, blockBits, Nat.cast_add]
    norm_num [div_eq_mul_inv]
    ring
  rw [arithmetic]
  exact (div_le_iff₀ (by positivity)).mpr castBound

end SimulatorMachine
end Kriterion.ArgoMAC.Security
