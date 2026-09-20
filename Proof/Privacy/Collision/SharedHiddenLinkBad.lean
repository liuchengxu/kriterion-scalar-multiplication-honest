import Proof.Privacy.Collision.HiddenLinkBad
import Proof.Privacy.Transcript.SharedLegacyTranscript

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The independent hidden key has the same exception bound for the actual shared transcript. -/
theorem sharedHiddenLinkBad_source_mass_le [Fintype BaseField] {Source : Type*}
    (samples : PMF Source) (curveResult : Source → BaseField)
    (transcript : Source → List (Sigma sharedRealOracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ source ∈ samples.support, (transcript source).length ≤ budget) :
    (samples.bind fun source => (PMF.uniformOfFintype BaseField).map (Prod.mk source)).toOuterMeasure
      {output | output.2 = curveResult output.1 ∨
        output.2 ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output.1))} ≤
      (1 + budget : ENNReal) / baseFieldModulus := by
  exact hiddenLinkBad_source_mass_le samples curveResult (fun source => sharedLegacyTranscript (transcript source))
    budget (fun source member => (sharedLegacyTranscript_length _).trans_le (lengthBound source member))

/-- An independent hidden key meets at most one field-sized exception per shared hash query. -/
theorem sharedHiddenHash_source_mass_le [Fintype BaseField] {Source : Type*}
    (samples : PMF Source)
    (transcript : Source → List (Sigma sharedRealOracleSpec.Answer)) (budget : Nat)
    (lengthBound : ∀ source ∈ samples.support, (transcript source).length ≤ budget) :
    (samples.bind fun source => (PMF.uniformOfFintype BaseField).map (Prod.mk source)).toOuterMeasure
      {output | output.2 ∈ transcriptHashInputs (sharedLegacyTranscript (transcript output.1))} ≤
      (budget : ENNReal) / baseFieldModulus := by
  apply Probability.bind_event_le
  intro source member
  rw [PMF.toOuterMeasure_map_apply]
  apply (uniform_hidden_transcript_hit (sharedLegacyTranscript (transcript source))).trans
  rw [sharedLegacyTranscript_length]
  exact ENNReal.div_le_div_right (by exact_mod_cast lengthBound source member) _

end
end Kriterion.ArgoMAC.Security
