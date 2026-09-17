import Proof.Privacy.Source.HiddenHashSource

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

attribute [local instance] Classical.propDecidable

variable [Fintype BaseField]

/-- These events exclude the zero mask and hidden hash queries. -/
def HiddenLinkBad (curveResult : BaseField)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (hidden : BaseField) : Prop :=
  hidden = curveResult ∨ hidden ∈ transcriptHashInputs transcript

/-- The hidden key has one shared bound for both exceptions. -/
theorem hiddenLinkBad_fixed_mass_le (curveResult : BaseField)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype BaseField).toOuterMeasure
      {hidden | HiddenLinkBad curveResult transcript hidden} ≤
        (1 + transcript.length : ENNReal) / baseFieldModulus := by
  have diagonal : (PMF.uniformOfFintype BaseField).toOuterMeasure {curveResult} =
      (1 : ENNReal) / baseFieldModulus := by
    rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    simp
  calc
    _ ≤ (PMF.uniformOfFintype BaseField).toOuterMeasure {curveResult} +
        (PMF.uniformOfFintype BaseField).toOuterMeasure
          {hidden | hidden ∈ transcriptHashInputs transcript} :=
      MeasureTheory.measure_union_le _ _
    _ ≤ 1 / (baseFieldModulus : ENNReal) + transcript.length / baseFieldModulus :=
      add_le_add diagonal.le (uniform_hidden_transcript_hit transcript)
    _ = _ := by rw [← ENNReal.add_div]

/-- An independent adaptive source preserves the hidden-key exception bound. -/
theorem hiddenLinkBad_source_mass_le {Source : Type*} (samples : PMF Source)
    (curveResult : Source → BaseField)
    (transcript : Source → List (Sigma Garbling.oracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ source ∈ samples.support, (transcript source).length ≤ budget) :
    (samples.bind fun source => (PMF.uniformOfFintype BaseField).map
      (Prod.mk source)).toOuterMeasure
        {output | HiddenLinkBad (curveResult output.1) (transcript output.1) output.2} ≤
      (1 + budget : ENNReal) / baseFieldModulus := by
  rw [PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  calc
    _ ≤ ∑' source, samples source * ((1 + budget : ENNReal) / baseFieldModulus) := by
      apply ENNReal.tsum_le_tsum
      intro source
      by_cases member : source ∈ samples.support
      · apply mul_le_mul_right
        apply (hiddenLinkBad_fixed_mass_le (curveResult source) (transcript source)).trans
        exact ENNReal.div_le_div_right
          (add_le_add_right (by exact_mod_cast lengthBound source member) 1) _
      · have zero : samples source = 0 := by rwa [PMF.apply_eq_zero_iff]
        simp [zero]
    _ = _ := by rw [ENNReal.tsum_mul_right, samples.tsum_coe, one_mul]

end

end Kriterion.ArgoMAC.Security
