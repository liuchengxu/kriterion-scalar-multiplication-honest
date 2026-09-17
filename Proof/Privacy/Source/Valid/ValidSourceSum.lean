import Proof.Privacy.Source.RealSourceLower
import Proof.Privacy.Source.SourceCapacity

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype
  residualFixedQueryDomainFintype transcriptOracleFintype

/-- A nonnegative label factor preserves the source lower bound. -/
theorem sourceScale_bound (a b x y : ℝ≥0∞) (bound : a * x ≤ y) : a * (b * x) ≤ b * y := by
  rw [mul_left_comm]
  exact mul_le_mul_right bound b

/-- This coin keeps the fields that determine the source flag. -/
def validSourceCoin (rest : GarblingSourceRest) (key : InputMacKey) : SimulatorCoin :=
  ⟨defaultSimulatorCoin.tableSample, rest.oracleCoin, key, rest.algebraic.field.bridgeKey⟩

/-- This schedule uses the actual linked labels and the retained source. -/
def validSourceSchedule [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (curveKey : InputMacKey) (tag : FullCircuitSource) : List GateDirective :=
  let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness) input
    (retainedFullSource rest tag)
  pipelineGateSchedule sample.curveRequest sample.pointRequests input (curveKey.encodeAffine input)
    ((EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey).encodeAffine input)

/-- This mass keeps the full tag and the conditional programmed post-query event. -/
def validProgrammedTagMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ℝ≥0∞ :=
  (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
    ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) * fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => programGateSchedule {state with fixedOracle := oracle.1}
          (validSourceSchedule rest outputKeys input curveKey tag))).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})

/-- This sum keeps the complete source tags with the observed table and a good prefix. -/
def validProgrammedSourceMass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] : ℝ≥0∞ :=
  ∑' tag : FullCircuitSource,
    if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬ rawSourceBad (validSourceCoin rest curveKey) (retainedFullSource rest tag) input before then
      validProgrammedTagMass rest outputKeys input curveKey state after tag else 0


end
end Kriterion.ArgoMAC.Security
