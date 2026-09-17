import Proof.Privacy.Source.LinkedGlobalSourceMass
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography FieldMacToECMac
open scoped ENNReal
noncomputable section

/-- The retained rest preserves every actual offset. -/
theorem sourceRest_reference_offsets [FieldCertificate] [GroupCertificate]
    (randomness : Garbling.Randomness) :
    (garblingOracleKeyEquiv randomness).2.reference.offsets = randomness.offsets := rfl

/-- The retained output-key event equals the actual public source event. -/
theorem realPublicSource_projection [FieldCertificate] [GroupCertificate]
    (witness : Garbling.Randomness) (parameter : Nat) (scalar : ScalarField)
    (table : Pipeline.Table) (input : AffineInput) (mac : InputMac)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    (randomTape witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (outputKeys construction scalar (garblingOracleKeyEquiv randomness).2.reference.offsets)
        randomness.pointRandomness randomness.bridgeKey randomness.curveMask randomness.curveR1
        randomness.curveR2 randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
        randomness.inputMacKey = table ∧ randomness.inputMacKey.encodeAffine input = mac ∧
        OracleTranscriptCompatible Garbling.oracleHandler randomness history} =
    (randomTape witness parameter).toOuterMeasure {randomness |
      Pipeline.garble (outputKeys construction scalar randomness.offsets)
        randomness.pointRandomness randomness.bridgeKey randomness.curveMask randomness.curveR1
        randomness.curveR2 randomness.fixedKeyOracle randomness.encPRFOracle randomness.hashOracle
        randomness.inputMacKey = table ∧ randomness.inputMacKey.encodeAffine input = mac ∧
        OracleTranscriptCompatible Garbling.oracleHandler randomness history} := by
  apply congrArg (randomTape witness parameter).toOuterMeasure
  ext randomness
  simp only [Set.mem_setOf_eq]
  rw [sourceRest_reference_offsets]

end
end Kriterion.ArgoMAC.Security
