import Proof.Privacy.Source.NonfixedSourceMass
import Proof.Privacy.Transcript.SharedLegacyTranscript

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The transcript adapter preserves exactly the nonfixed public constraints. -/
theorem sharedLegacyTranscript_nonfixed (randomness : Garbling.Randomness)
    (fixed : PermutationOracle Shared.FixedKeyIndex Block)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    NonFixedTranscriptCompatible randomness (sharedLegacyTranscript transcript) ↔
      SharedNonFixedTranscriptCompatible (fixed, randomness.encPRFOracle, randomness.hashOracle) transcript := by
  induction transcript with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [sharedLegacyTranscript, List.map_cons, sharedLegacyEntry,
          NonFixedTranscriptCompatible, SharedNonFixedTranscriptCompatible]
      all_goals first | exact ih | exact and_congr Iff.rfl ih

/-- The exact EncPRF factor is the shared nonfixed oracle average. -/
theorem sharedNonfixedEncHash_weighted_eq [Fintype Block] [Fintype BaseField]
    (randomness : Garbling.Randomness) (fixed : PermutationOracle Shared.FixedKeyIndex Block)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (reference : PermutationTranscriptMatches randomness.encPRFOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript transcript)))
    (weight : EncPRF.HashOracle → ENNReal) :
    encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript)) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if SharedNonFixedTranscriptCompatible (fixed, randomness.encPRFOracle, hash) transcript then weight hash else 0) =
    ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          if SharedNonFixedTranscriptCompatible (fixed, enc, hash) transcript then weight hash else 0 := by
  have law := nonfixedEncHash_weighted_eq randomness (sharedLegacyTranscript transcript) reference weight
  simp_rw [sharedLegacyTranscript_nonfixed _ fixed] at law
  exact law

end
end Kriterion.ArgoMAC.Security
