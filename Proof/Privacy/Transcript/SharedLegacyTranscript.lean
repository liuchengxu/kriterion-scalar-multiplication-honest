import Proof.Privacy.Transcript.SharedPublicTranscript
import Proof.Privacy.Source.LinkedTagSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- This adapter uses one legacy name for each actual shared slot. -/
def sharedLegacyEntry : Sigma sharedRealOracleSpec.Answer → Sigma Garbling.oracleSpec.Answer
  | ⟨.fixedForward index input, output⟩ =>
      ⟨.fixedForward ⟨index.kind, index.position, .hash index.slot⟩ input, output⟩
  | ⟨.fixedInverse index output, input⟩ =>
      ⟨.fixedInverse ⟨index.kind, index.position, .hash index.slot⟩ output, input⟩
  | ⟨.encForward index input, output⟩ => ⟨.encForward index input, output⟩
  | ⟨.encInverse index output, input⟩ => ⟨.encInverse index output, input⟩
  | ⟨.hash input, output⟩ => ⟨.hash input, output⟩

/-- The adapter preserves every actual query and its answer. -/
def sharedLegacyTranscript (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    List (Sigma Garbling.oracleSpec.Answer) := transcript.map sharedLegacyEntry

/-- The adapter preserves the public query count. -/
theorem sharedLegacyTranscript_length (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (sharedLegacyTranscript transcript).length = transcript.length := List.length_map _

/-- The adapter preserves the split between the two adaptive query phases. -/
theorem sharedLegacyTranscript_append (first second : List (Sigma sharedRealOracleSpec.Answer)) :
    sharedLegacyTranscript (first ++ second) = sharedLegacyTranscript first ++ sharedLegacyTranscript second :=
  List.map_append

/-- The legacy reference reads exactly the shared public answers through the adapter. -/
theorem sharedLegacyTranscript_compatible (randomness : Garbling.Randomness)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible Garbling.oracleHandler randomness (sharedLegacyTranscript transcript) ↔
      OracleTranscriptCompatible (publicHandler id)
        (Shared.restrictOracle randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle) transcript := by
  induction transcript with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [sharedLegacyTranscript, List.map_cons, sharedLegacyEntry, OracleTranscriptCompatible, Garbling.oracleHandler, publicHandler]
      all_goals exact and_congr Iff.rfl ih

/-- A shared fixed oracle keeps its exact public transcript in the legacy source theorem. -/
theorem sharedLegacyTranscript_expand (randomness : Garbling.Randomness)
    (fixed : PermutationOracle Shared.FixedKeyIndex Block)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with fixedKeyOracle := Shared.expandOracle fixed} (sharedLegacyTranscript transcript) ↔
      OracleTranscriptCompatible (publicHandler id) (fixed, randomness.encPRFOracle, randomness.hashOracle) transcript := by
  rw [sharedLegacyTranscript_compatible]
  simp only [Shared.restrict_expand]

end
end Kriterion.ArgoMAC.Security
