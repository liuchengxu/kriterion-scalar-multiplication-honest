import Proof.Privacy.Source.Valid.ValidSourceSumRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A source subtype embeds into the complete retained tape sum. -/
theorem weightedSubtypeMass_lower {Source : Type}
    (weights : Source → ℝ≥0∞) (factor : ℝ≥0∞) (kept : Source → Prop)
    (sourceMass : {source // kept source} → ℝ≥0∞) (realMass : Source → ℝ≥0∞)
    (bound : ∀ source, factor * sourceMass source ≤ realMass source.1) :
    factor * (∑' source : {source // kept source}, weights source.1 * sourceMass source) ≤
      ∑' source, weights source * realMass source := by
  rw [← ENNReal.tsum_mul_left]
  apply le_trans (ENNReal.tsum_le_tsum fun source => ?_)
    (ENNReal.summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ => bot_le) (fun _ => le_rfl) ENNReal.summable)
  calc
    factor * (weights source.1 * sourceMass source) = weights source.1 * (factor * sourceMass source) := by ac_rfl
    _ ≤ _ := mul_le_mul_right (bound source) (weights source.1)


set_option maxRecDepth 4096 in
/-- The valid complete-source sum is below the full actual random-tape public event. -/
def validGlobalSourceMass_real_le [fieldCert : FieldCertificate] [groupCert : GroupCertificate] [blockFinite : Fintype Block]
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
    _
    (fun rest => retainedRealPublicMass rest (outputKeys rest) table input
      (curveKey.encodeAffine input) (before ++ after))
    (fun rest => @validProgrammedSourceMass_real_le fieldCert groupCert blockFinite
      rest.1 (outputKeys rest.1) table input curveKey (state rest.1) before after
      (oracleExists rest.1) valid rest.2 (members rest.1) queries small lengthBound)
  le_trans bound (le_of_eq (realTapePublicMass_split witness parameter outputKeys table input
    (curveKey.encodeAffine input) (before ++ after)).symm)

end
end Kriterion.ArgoMAC.Security
