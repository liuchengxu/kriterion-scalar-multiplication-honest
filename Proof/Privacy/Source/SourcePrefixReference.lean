import Proof.Privacy.Source.Valid.ValidSourceNormalization

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Equal fixed oracles and initial records give equal final fixed records. -/
theorem idealTranscriptFinal_fixedHistory_eq (state other : SimulatorState)
    (history : List (Sigma Garbling.oracleSpec.Answer))
    (sameFixed : state.fixedOracle = other.fixedOracle)
    (sameHistory : state.fixedTranscript = other.fixedTranscript) :
    (transcriptFinalState idealOracleHandler state history).fixedTranscript =
      (transcriptFinalState idealOracleHandler other history).fixedTranscript := by
  induction history generalizing state other with
  | nil => exact sameHistory
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      simp only [transcriptFinalState]
      cases request <;> apply inductionHypothesis <;>
        simp only [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash,
          sameFixed, sameHistory]

private theorem idealTranscript_fixed_matches (state : SimulatorState)
    (randomness : Garbling.Randomness) (history : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state history) :
    PermutationTranscriptMatches state.fixedOracle (fixedOracleTranscriptRecords history) := by
  have real := (idealOracleTranscriptCompatible_iff_real state
    {randomness with fixedKeyOracle := state.fixedOracle, encPRFOracle := state.encOracle, hashOracle := state.hashOracle} history rfl rfl rfl).mp compatible
  rw [realOracleTranscriptCompatible_iff] at real
  exact real.1

/-- This initial state keeps the common fixed oracle and each retained nonfixed oracle. -/
def sourcePrefixReference (reference : SimulatorState) (rest : GarblingSourceRest) : SimulatorState :=
  initialSourceOracle ⟨reference.fixedOracle, defaultSimulatorCoin.inputKey, rest.encPRFOracle, rest.hashOracle⟩

/-- The common fixed oracle gives a compatible prefix when the retained nonfixed replies match. -/
theorem sourcePrefixReference_compatible (reference : SimulatorState) (rest : GarblingSourceRest)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference before) :
    OracleTranscriptCompatible idealOracleHandler (sourcePrefixReference reference rest) before := by
  apply (idealCompatible_iff_fixed_of_nonfixed (sourcePrefixReference reference rest)
    rest.reference before rfl rfl nonfixed).mpr
  exact idealTranscript_fixed_matches reference rest.reference before compatible

/-- Every retained source has the same complete fixed prefix history. -/
theorem sourcePrefixReference_history (reference : SimulatorState) (rest : GarblingSourceRest)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before) :
    (transcriptFinalState idealOracleHandler (sourcePrefixReference reference rest) before).fixedTranscript =
      (fixedOracleTranscriptRecords before).reverse := by
  let initial := initialSourceOracle
    (⟨reference.fixedOracle, defaultSimulatorCoin.inputKey, reference.encOracle, reference.hashOracle⟩ : GarblingOracleData)
  let randomness := {rest.reference with fixedKeyOracle := reference.fixedOracle, encPRFOracle := reference.encOracle, hashOracle := reference.hashOracle}
  have first := (idealOracleTranscriptCompatible_iff_real reference randomness before rfl rfl rfl).mp compatible
  have initialCompatible := (idealOracleTranscriptCompatible_iff_real initial randomness before rfl rfl rfl).mpr first
  have same := idealTranscriptFinal_fixedHistory_eq (sourcePrefixReference reference rest) initial before rfl rfl
  rw [same, idealTranscriptFinal_fixedHistory initial before initialCompatible]
  exact List.append_nil _

/-- Every retained source has exactly the externally recorded fixed prefix members. -/
theorem sourcePrefixReference_members (reference : SimulatorState) (rest : GarblingSourceRest)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ (transcriptFinalState idealOracleHandler (sourcePrefixReference reference rest) before).fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords before := by
  rw [sourcePrefixReference_history reference rest before compatible, List.mem_reverse]

/-- The common fixed oracle inhabits every retained prefix fiber. -/
theorem sourcePrefixReference_oracleExists (reference : SimulatorState) (rest : GarblingSourceRest)
    (before : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before) :
    Nonempty (TranscriptOracle
      (transcriptFinalState idealOracleHandler (sourcePrefixReference reference rest) before).fixedTranscript) := by
  refine ⟨⟨reference.fixedOracle, ?_⟩⟩
  rw [sourcePrefixReference_history reference rest before compatible]
  have matchesBefore := idealTranscript_fixed_matches reference rest.reference before compatible
  simpa only [PermutationTranscriptMatches, List.mem_reverse] using matchesBefore

end
end Kriterion.ArgoMAC.Security
