import Proof.Privacy.Source.Valid.ValidSourceSum
import Proof.Privacy.Source.ProductSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype instFintypeCircuitMaskTables
  instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 fixedQueryDomainFintype
  residualFixedQueryDomainFintype transcriptOracleFintype

/-- The good source flag supplies every raw count premise on valid inputs. -/
def validRawProgrammedSourceRatio [Fintype Block]
    (rest : GarblingSourceRest) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (curveKey : InputMacKey)
    (state : SimulatorState) (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (valid : OnCurve input) (good : ¬rawSourceBad (validSourceCoin rest curveKey) source input before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :=
  linkedHiddenSourceMass_product_ge_of_nonfixed rest rows input source curveKey state before after
    nonfixed
    (rawSourceGood_offsets (validSourceCoin rest curveKey) source input before good)
    members
    (rawSourceGood_pipeline (validSourceCoin rest curveKey) state rest.algebraic.field.curveMask.value
      rows source input before members valid good)
    (sourcePriorCapacity state before members queries small
      ((Nat.le_add_right before.length after.length).trans (by simpa only [List.length_append] using lengthBound)))
    (sourceResidualCapacity (before ++ after) _ queries small lengthBound)

/-- Each good valid tag gives the actual real hidden-label lower bound. -/
def validProgrammedTagMass_real_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullCircuitSource)
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (valid : OnCurve input) (complete : FullSourceComplete tag.1)
    (good : ¬ rawSourceBad (validSourceCoin rest curveKey) (retainedFullSource rest tag) input before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :=
  let ratio := validRawProgrammedSourceRatio rest
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    input (retainedFullSource rest tag) curveKey state before after valid good nonfixed members
    queries small lengthBound
  let moved := le_trans ratio (le_of_eq (congrArg
    (fun lifts => linkedHiddenSourceMass rest (retainedFullSource rest tag) lifts input
      (curveKey.encodeAffine input) (before ++ after))
    (retainedFullSource_lifts rest tag complete)))
  sourceScale_bound _ ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹) _ _ moved

/-- A restricted sum preserves every pointwise source lower bound. -/
theorem restrictedTagMass_lower {Tag : Type} (factor target : ℝ≥0∞)
    (tagMass realMass : Tag → ℝ≥0∞) (kept broader : Tag → Prop)
    [DecidablePred kept] [DecidablePred broader]
    (included : ∀ tag, kept tag → broader tag)
    (bound : ∀ tag, kept tag → factor * tagMass tag ≤ realMass tag)
    (total : (∑' tag, if broader tag then realMass tag else 0) ≤ target) :
    factor * (∑' tag, if kept tag then tagMass tag else 0) ≤ target := by
  classical
  rw [← ENNReal.tsum_mul_left]
  apply le_trans (ENNReal.tsum_le_tsum fun tag => ?_) total
  by_cases good : kept tag
  · rw [if_pos good, if_pos (included tag good)]
    exact bound tag good
  · rw [if_neg good, mul_zero]
    exact bot_le

set_option maxRecDepth 4096 in
/-- The complete good-tag sum is below the actual valid public event. -/
def validProgrammedSourceMass_real_le [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (curveKey : InputMacKey) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (valid : OnCurve input) (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (queries : Nat) (small : queries < 2 ^ 100) (lengthBound : (before ++ after).length ≤ queries) :=
  restrictedTagMass_lower
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞))
    (retainedRealPublicMass rest outputKeys table input (curveKey.encodeAffine input) (before ++ after))
    _
    (fun tag => (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      linkedHiddenSourceMass rest (retainedFullSource rest tag) tag.1 input
        (curveKey.encodeAffine input) (before ++ after))
    (fun tag => FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table ∧
      ¬rawSourceBad (validSourceCoin rest curveKey) (retainedFullSource rest tag) input before)
    (fun tag => FullSourceComplete tag.1 ∧ retainedFullTable rest outputKeys tag = table)
    (fun _ kept => ⟨kept.1, kept.2.1⟩)
    (fun tag kept => validProgrammedTagMass_real_le rest outputKeys input curveKey state before after tag
      valid kept.1 kept.2.2 nonfixed members queries small lengthBound)
    (retainedRealSource_fullTag_sum_le rest outputKeys table input (curveKey.encodeAffine input) (before ++ after))

end
end Kriterion.ArgoMAC.Security
