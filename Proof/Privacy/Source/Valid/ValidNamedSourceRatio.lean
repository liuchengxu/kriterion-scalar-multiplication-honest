import Proof.Privacy.Source.Valid.ValidGlobalSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype
  residualFixedQueryDomainFintype transcriptOracleFintype

/-- The callback equality expands the actual source schedule. -/
theorem validProgrammedTagMass_formula
    [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    validProgrammedTagMass rest outputKeys input curveKey state after tag =
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => programGateSchedule {state with fixedOracle := oracle.1}
            (pipelineGateSchedule
              (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
                (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
                input (retainedFullSource rest tag)).curveRequest
              (circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value
                (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
                input (retainedFullSource rest tag)).pointRequests
              input (curveKey.encodeAffine input)
              ((EncPRF.transformKey rest.encPRFOracle
                (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey).encodeAffine input)))).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) := by
  unfold validProgrammedTagMass
  apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * ·)
  apply congrArg (((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
    fixedTranscriptFactor state.fixedTranscript) * ·)
  apply congrArg (fun samples : PMF SimulatorState => samples.toOuterMeasure
    {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})
  apply congrArg (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
  funext oracle
  rfl

set_option maxRecDepth 4096 in
/-- The named source mass has the checked complete-tag lower bound. -/
theorem validProgrammedSourceMass_named_le
    [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [oracleExists : Nonempty (TranscriptOracle state.fixedTranscript)]
    (valid : OnCurve input) (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      validProgrammedSourceMass rest outputKeys table input curveKey state before after ≤
      retainedRealPublicMass rest outputKeys table input (curveKey.encodeAffine input) (before ++ after) := by
  have namedEq := congrArg
    (fun tagMass : FullCircuitSource → ℝ≥0∞ => ∑' tag,
      if FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
        ¬ rawSourceBad (validSourceCoin rest curveKey) (retainedFullSource rest tag) input before then
        tagMass tag else 0)
    (funext (fun tag => @validProgrammedTagMass_formula fieldCert groupCert blockFinite
      rest outputKeys input curveKey state after tag oracleExists))
  exact le_trans (le_of_eq (congrArg
    ((1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) * ·) namedEq))
    (@validProgrammedSourceMass_real_le fieldCert groupCert blockFinite rest outputKeys
      table input curveKey state before after oracleExists valid nonfixed members queries small lengthBound)


set_option maxRecDepth 4096 in
/-- The valid complete-source sum is below the full actual random-tape public event. -/
def validGlobalSourceMass_named_le [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
    (witness : Garbling.Randomness) (parameter : Nat)
    (outputKeys : GarblingSourceRest → FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (curveKey : InputMacKey)
    (state : GarblingSourceRest → SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (oracleExists : ∀ rest, Nonempty (TranscriptOracle (state rest).fixedTranscript))
    (valid : OnCurve input)
    (members : ∀ rest record, record ∈ (state rest).fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :=
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  let bound := weightedSubtypeMass_lower
    (fun rest : GarblingSourceRest => (PMF.uniformOfFintype GarblingSourceRest) rest)
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞))
    (fun rest => NonFixedTranscriptCompatible rest.reference (before ++ after))
    (fun rest => @validProgrammedSourceMass fieldCert groupCert blockFinite rest.1
      (outputKeys rest.1) table input curveKey (state rest.1) before after (oracleExists rest.1))
    (fun rest => retainedRealPublicMass rest (outputKeys rest) table input
      (curveKey.encodeAffine input) (before ++ after))
    (fun rest => @validProgrammedSourceMass_named_le fieldCert groupCert blockFinite
      rest.1 (outputKeys rest.1) table input curveKey (state rest.1) before after
      (oracleExists rest.1) valid rest.2 (members rest.1) queries small lengthBound)
  le_trans bound (le_of_eq (realTapePublicMass_split witness parameter outputKeys table input
    (curveKey.encodeAffine input) (before ++ after)).symm)


end
end Kriterion.ArgoMAC.Security
