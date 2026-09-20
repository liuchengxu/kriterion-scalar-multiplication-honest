import Proof.Privacy.Transcript.SharedIdealGateGame
import Proof.Privacy.Simulator.SharedFixedStateCongr

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- This initial state keeps the common fixed oracle and each retained nonfixed oracle. -/
def sharedSourcePrefixReference (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) : Shared.Simulator.OracleState :=
  { fixedOracle := reference.fixedOracle
    encOracle := rest.encPRFOracle
    hashOracle := rest.hashOracle
    fixedTranscript := []
    encTranscript := []
    hashTranscript := []
    commitments := []
    linking := none
    bad := false }

/-- Every source reference starts with the exact empty-history invariant. -/
theorem sharedSourcePrefixReference_invariant (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) : SimulatorInvariant (sharedSourcePrefixReference reference rest) := by
  simp [sharedSourcePrefixReference, SimulatorInvariant, PermutationTranscriptMatches,
    HashTranscriptMatches, DistinctCommitments]

/-- The common fixed oracle gives a compatible prefix when the retained nonfixed replies match. -/
theorem sharedSourcePrefixReference_compatible (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) (before : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (reference.fixedOracle, rest.encPRFOracle, rest.hashOracle) before) :
    OracleTranscriptCompatible idealOracleHandler (sharedSourcePrefixReference reference rest) before := by
  rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff] at compatible ⊢
  exact ⟨compatible.1, nonfixed⟩

/-- Every retained source has the same complete fixed prefix history. -/
theorem sharedSourcePrefixReference_history (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) (before : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before) :
    (transcriptFinalState idealOracleHandler (sharedSourcePrefixReference reference rest) before).fixedTranscript =
      (sharedFixedTranscriptRecords before).reverse := by
  let initial : Shared.Simulator.OracleState := {reference with fixedTranscript := []}
  have initialCompatible : OracleTranscriptCompatible idealOracleHandler initial before := by
    rw [sharedIdealTranscriptCompatible_iff] at compatible ⊢
    exact compatible
  have same := (sharedIdealTranscriptFinal_fixed_fields
    (sharedSourcePrefixReference reference rest) initial before rfl rfl).2
  rw [same, sharedIdealTranscriptFinal_fixedHistory initial before initialCompatible]
  exact List.append_nil _

/-- Every retained source has exactly the externally recorded fixed prefix members. -/
theorem sharedSourcePrefixReference_members (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) (before : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (record : PermutationRecord Shared.FixedKeyIndex Block) :
    record ∈ (transcriptFinalState idealOracleHandler (sharedSourcePrefixReference reference rest) before).fixedTranscript ↔
      record ∈ sharedFixedTranscriptRecords before := by
  rw [sharedSourcePrefixReference_history reference rest before compatible, List.mem_reverse]

end
end Kriterion.ArgoMAC.Security
