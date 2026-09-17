import Proof.Privacy.Transcript.EncPRFGame

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An exact source map preserves every nonnegative weighted sum. -/
theorem pmf_map_weighted_sum {Source Target : Type*} (samples : PMF Source)
    (project : Source → Target) (weight : Target → ENNReal) :
    (∑' target, (samples.map project) target * weight target) =
      ∑' source, samples source * weight (project source) := by
  classical
  simp_rw [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro source
  rw [tsum_eq_single (project source)]
  · simp
  · intro target different
    simp [different]

variable [Fintype Block] [Fintype BaseField]

/-- Resampling the hidden hash answer preserves arbitrary source weights exactly. -/
theorem uniformHashAt_weighted (hidden : BaseField)
    (weight : EncPRF.HashOracle → (Block × Block) → ENNReal) :
    (∑' sample : EncPRF.HashOracle × (Block × Block),
      (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))) sample *
        weight (Function.update sample.1 hidden sample.2) sample.2) =
    ∑' hash : EncPRF.HashOracle,
      (PMF.uniformOfFintype EncPRF.HashOracle) hash * weight hash (hash hidden) := by
  have law := congrArg (fun distribution => ∑' hash : EncPRF.HashOracle,
    distribution hash * weight hash (hash hidden)) (map_uniform_hash_resample hidden)
  simp only [pmf_map_weighted_sum] at law
  simpa only [Function.update_self] using law

/-- A transcript that misses the hidden input permits an exact fresh-answer source count. -/
theorem hiddenHashTranscript_weighted_eq (hidden : BaseField) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : hidden ∉ transcriptHashInputs transcript) (weight : (Block × Block) → ENNReal) :
    (∑' hash : EncPRF.HashOracle,
      (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        (if OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := hash} transcript
          then weight (hash hidden) else 0)) =
    ∑' sample : EncPRF.HashOracle × (Block × Block),
      (PMF.uniformOfFintype (EncPRF.HashOracle × (Block × Block))) sample *
        (if OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := sample.1} transcript
          then weight sample.2 else 0) := by
  classical
  have compatible (hash : EncPRF.HashOracle) (answer : Block × Block) :
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with hashOracle := Function.update hash hidden answer} transcript ↔
      OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := hash} transcript := by
    simpa only [replaceHashAt] using replaceHashAt_compatible
      {randomness with hashOracle := hash} hidden answer transcript miss
  have law := uniformHashAt_weighted hidden (fun hash answer =>
    if OracleTranscriptCompatible Garbling.oracleHandler {randomness with hashOracle := hash} transcript
      then weight answer else 0)
  simp only [compatible] at law
  exact law.symm

end

end Kriterion.ArgoMAC.Security
