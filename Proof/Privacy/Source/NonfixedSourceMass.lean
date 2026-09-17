import Proof.Privacy.Transcript.EncPRFTranscript
import Proof.Privacy.Source.HiddenHashSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 2048 in
/-- A compatible EncPRF reference separates the exact nonfixed constraints. -/
theorem nonfixedTranscript_update_enc_factor (randomness : Garbling.Randomness)
    (oracle : PermutationOracle EncPRF.PermutationIndex Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle (encOracleTranscriptRecords transcript)) :
    NonFixedTranscriptCompatible {randomness with encPRFOracle := oracle} transcript ↔
      NonFixedTranscriptCompatible randomness transcript ∧
        PermutationTranscriptMatches oracle (encOracleTranscriptRecords transcript) := by
  have inverse (permutation : Equiv.Perm Block) (input output : Block) :
      permutation.symm output = input ↔ permutation input = output := by
    constructor
    · intro same
      rw [← same, Equiv.apply_symm_apply]
    · intro same
      rw [← same, Equiv.symm_apply_apply]
  have matchesCons (enc : PermutationOracle EncPRF.PermutationIndex Block)
      (record : PermutationRecord EncPRF.PermutationIndex Block) (tail) :
      PermutationTranscriptMatches enc (record :: tail) ↔
        enc.permutation record.index record.domain = record.range ∧ PermutationTranscriptMatches enc tail := by
    simp [PermutationTranscriptMatches]
  induction transcript with
  | nil => simp [NonFixedTranscriptCompatible, PermutationTranscriptMatches, encOracleTranscriptRecords]
  | cons entry tail ih =>
      rcases entry with ⟨query, answer⟩
      cases query with
      | fixedForward index value => exact ih reference
      | fixedInverse index value => exact ih reference
      | encForward index value =>
          simp only [encOracleTranscriptRecords, matchesCons] at reference
          simp only [NonFixedTranscriptCompatible, encOracleTranscriptRecords, matchesCons,
            ih reference.2, reference.1, true_and]
          simp [inverse, reference.1, and_left_comm]
          exact fun _ _ _ => rfl
      | encInverse index value =>
          simp only [encOracleTranscriptRecords, matchesCons] at reference
          simp only [NonFixedTranscriptCompatible, encOracleTranscriptRecords, matchesCons, inverse,
            ih reference.2, reference.1, true_and]
          rw [inverse (oracle.permutation index) answer value,
            inverse (randomness.encPRFOracle.permutation index) answer value, reference.1]
          simp [and_left_comm, and_assoc]
      | hash value =>
          simp only [encOracleTranscriptRecords] at reference ⊢
          simp only [NonFixedTranscriptCompatible, ih reference]
          exact and_assoc.symm


/-- The exact nonfixed average contains one EncPRF transcript factor. -/
theorem nonfixedEncHash_weighted_eq [Fintype Block] [Fintype BaseField]
    (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle (encOracleTranscriptRecords transcript))
    (weight : EncPRF.HashOracle → ℝ≥0∞) :
    encTranscriptFactor (encOracleTranscriptRecords transcript) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if NonFixedTranscriptCompatible {randomness with hashOracle := hash} transcript then weight hash else 0) =
    ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      ∑' oracle : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) oracle *
          if NonFixedTranscriptCompatible
            {randomness with encPRFOracle := oracle, hashOracle := hash} transcript then weight hash else 0 := by
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro hash
  have separate (oracle : PermutationOracle EncPRF.PermutationIndex Block) :=
    nonfixedTranscript_update_enc_factor {randomness with hashOracle := hash} oracle transcript reference
  conv_rhs =>
    arg 2
    arg 1
    ext oracle
    arg 2
    rw [separate oracle]
  by_cases compatible : NonFixedTranscriptCompatible {randomness with hashOracle := hash} transcript
  · simp only [compatible, if_true, true_and]
    rw [← encTranscriptFactor_eq_mass randomness.encPRFOracle _ reference,
      PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro oracle
    by_cases matching : PermutationTranscriptMatches oracle (encOracleTranscriptRecords transcript)
    · simp [Set.indicator, matching, mul_assoc, mul_comm, mul_left_comm]
    · simp [Set.indicator, matching]
  · simp [compatible]

end
end Kriterion.ArgoMAC.Security
