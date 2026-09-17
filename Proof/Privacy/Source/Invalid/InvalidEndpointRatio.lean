import Proof.Privacy.Source.Invalid.InvalidGlobalSourceRatio
import Proof.Privacy.Source.RealSourceProjection

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A relative source bound preserves the common phase factor. -/
theorem phase_relative_bound (ghost mass publicMass real factor phase : ℝ≥0∞)
    (ghostBound : ghost ≤ phase * mass) (sourceBound : factor * mass ≤ publicMass)
    (realEq : real = phase * publicMass) : factor * ghost ≤ real := by
  rw [realEq]
  calc
    factor * ghost ≤ factor * (phase * mass) := mul_le_mul_right ghostBound factor
    _ = phase * (factor * mass) := by ac_rfl
    _ ≤ phase * publicMass := mul_le_mul_right sourceBound phase

set_option maxRecDepth 4096 in
/-- The real transcript equals its common phase factor and actual retained public event. -/
theorem realAdaptiveTranscript_retained_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (table : Pipeline.Table) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (key : InputMacKey)
    (bits : labels.input = BitInput.ofAffine selected.1)
    (mac : key.encodeAffine selected.1 = labels.inputMac)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (realAdaptiveTranscriptWithState (Garbling.garbledCircuit construction)
      (randomTape witness) Garbling.oracleHandler adversary parameter scalar auxiliary)
        (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (randomTape witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (actualSourceOutputKeys scalar.value (garblingOracleKeyEquiv randomness).2)
        randomness.pointRandomness randomness.bridgeKey randomness.curveMask randomness.curveR1
        randomness.curveR2 randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
        randomness.inputMacKey = table ∧ randomness.inputMacKey.encodeAffine selected.1 = key.encodeAffine selected.1 ∧
        OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after)} := by
  rw [realAdaptiveTranscript_mass_factor adversary parameter auxiliary scalar witness table referenceBefore referenceAfter
    selected labels decision before after firstCompatible secondCompatible, if_pos bits]
  apply congrArg (((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) * ·)
  apply congrArg (randomTape witness parameter).toOuterMeasure
  ext randomness
  simp only [Set.mem_setOf_eq, actualSourceOutputKeys, sourceRest_reference_offsets, mac]

end
end Kriterion.ArgoMAC.Security
