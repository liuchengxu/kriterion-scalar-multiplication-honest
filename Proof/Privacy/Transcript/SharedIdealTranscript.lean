import Proof.Privacy.Simulator.SharedSimulator
import Proof.Privacy.Transcript.SharedPublicTranscript
import Proof.Privacy.Transcript.AdaptiveGameRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Both shared transcript phases retain the same nonfixed oracle constraints. -/
theorem sharedNonFixedTranscriptCompatible_append
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) :
    SharedNonFixedTranscriptCompatible oracle (before ++ after) ↔
      SharedNonFixedTranscriptCompatible oracle before ∧ SharedNonFixedTranscriptCompatible oracle after := by
  induction before with
  | nil => simp [SharedNonFixedTranscriptCompatible]
  | cons entry remaining ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [List.cons_append, SharedNonFixedTranscriptCompatible, ih, and_assoc]

/-- The recording handler gives the same answers as the shared public oracle. -/
theorem sharedIdealTranscriptCompatible_iff (state : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible idealOracleHandler state transcript ↔
      OracleTranscriptCompatible (publicHandler id)
        (state.fixedOracle, state.encOracle, state.hashOracle) transcript := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry remaining ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [OracleTranscriptCompatible, idealOracleHandler, oracleHandlerFor,
          publicHandler, publicAnswer]
      all_goals exact and_congr Iff.rfl (ih _)

/-- The shared recording handler retains the complete fixed query history. -/
theorem sharedIdealTranscriptFinal_fixedHistory (state : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state transcript) :
    (transcriptFinalState idealOracleHandler state transcript).fixedTranscript =
      (sharedFixedTranscriptRecords transcript).reverse ++ state.fixedTranscript := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨request, answer⟩
      simp only [idealOracleHandler] at ih
      cases request <;>
        simp only [OracleTranscriptCompatible, idealOracleHandler, oracleHandlerFor] at compatible
      all_goals
        simp only [transcriptFinalState, idealOracleHandler, oracleHandlerFor]
        rw [ih _ compatible.2]
        simp only [sharedFixedTranscriptRecords, recordFixed, recordEnc, recordHash,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        try rw [compatible.1]

/-- The shared transcript preserves all three oracle functions. -/
theorem sharedIdealTranscriptFinal_oracles (state : Shared.Simulator.OracleState)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (transcriptFinalState idealOracleHandler state transcript).fixedOracle = state.fixedOracle ∧
    (transcriptFinalState idealOracleHandler state transcript).encOracle = state.encOracle ∧
      (transcriptFinalState idealOracleHandler state transcript).hashOracle = state.hashOracle := by
  induction transcript generalizing state with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons entry tail ih =>
      have result := ih (idealOracleHandler entry.1 state).2
      rcases entry with ⟨request, answer⟩
      cases request <;> exact result

/-- Equal fixed answers give the same shared recorded state fields. -/
theorem sharedIdealHandler_updateFixed (state : Shared.Simulator.OracleState)
    (oracle : PermutationOracle Shared.FixedKeyIndex Block) (query : sharedRealOracleSpec.Query)
    (same : (idealOracleHandler query {state with fixedOracle := oracle}).1 =
      (idealOracleHandler query state).1) :
    (idealOracleHandler query {state with fixedOracle := oracle}).2 =
      {(idealOracleHandler query state).2 with fixedOracle := oracle} := by
  cases query <;>
    simp only [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash] at same ⊢
  all_goals try rw [same]

/-- A compatible shared prefix keeps its recorded fields when the fixed oracle changes. -/
theorem sharedIdealTranscriptFinal_updateFixed (state : Shared.Simulator.OracleState)
    (oracle : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state history)
    (updated : OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} history) :
    transcriptFinalState idealOracleHandler {state with fixedOracle := oracle} history =
      {transcriptFinalState idealOracleHandler state history with fixedOracle := oracle} := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨query, answer⟩
      change _ ∧ _ at compatible updated
      have next := sharedIdealHandler_updateFixed state oracle query (updated.1.trans compatible.1.symm)
      simp only [transcriptFinalState]
      rw [next]
      apply ih _ compatible.2
      rw [← next]
      exact updated.2

/-- A compatible shared prefix fixes exactly its recorded permutation equations. -/
theorem sharedIdealPrefixCompatible_iff_matches (state : Shared.Simulator.OracleState)
    (before : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state before)
    (oracle : PermutationOracle Shared.FixedKeyIndex Block) :
    OracleTranscriptCompatible idealOracleHandler {state with fixedOracle := oracle} before ↔
      PermutationTranscriptMatches oracle (sharedFixedTranscriptRecords before) := by
  rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff] at compatible ⊢
  have other := (sharedNonFixedTranscriptCompatible_fixed oracle state.fixedOracle
    state.encOracle state.hashOracle before).mpr compatible.2
  exact and_iff_left other

/-- The public transcript and recorded prefix differ only in record order. -/
theorem sharedIdealTranscriptFinal_fullPermutation (state : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (empty : state.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler state before) :
    (sharedFixedTranscriptRecords (before ++ after)).Perm
      ((transcriptFinalState idealOracleHandler state before).fixedTranscript ++
        sharedFixedTranscriptRecords after) := by
  rw [sharedFixedTranscriptRecords_append, sharedIdealTranscriptFinal_fixedHistory state before compatible,
    empty, List.append_nil]
  exact (List.reverse_perm _).symm.append_right _

end
end Kriterion.ArgoMAC.Security
