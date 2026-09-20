import Proof.Privacy.Source.SharedRealSourceSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- This function extracts both directions of the real fixed-oracle interaction. -/
def sharedFixedTranscriptRecords : List (Sigma sharedRealOracleSpec.Answer) →
    List (PermutationRecord Shared.FixedKeyIndex Block)
  | [] => []
  | ⟨.fixedForward index input, output⟩ :: remaining =>
      ⟨.forward, .adversary, index, input, output⟩ :: sharedFixedTranscriptRecords remaining
  | ⟨.fixedInverse index output, input⟩ :: remaining =>
      ⟨.inverse, .adversary, index, input, output⟩ :: sharedFixedTranscriptRecords remaining
  | ⟨.encForward _ _, _⟩ :: remaining => sharedFixedTranscriptRecords remaining
  | ⟨.encInverse _ _, _⟩ :: remaining => sharedFixedTranscriptRecords remaining
  | ⟨.hash _, _⟩ :: remaining => sharedFixedTranscriptRecords remaining

/-- This condition fixes the other actual oracle answers while the fixed family varies. -/
def SharedNonFixedTranscriptCompatible (randomness : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    List (Sigma sharedRealOracleSpec.Answer) → Prop
  | [] => True
  | ⟨.fixedForward _ _, _⟩ :: remaining => SharedNonFixedTranscriptCompatible randomness remaining
  | ⟨.fixedInverse _ _, _⟩ :: remaining => SharedNonFixedTranscriptCompatible randomness remaining
  | ⟨.encForward index input, output⟩ :: remaining =>
      randomness.2.1.permutation index input = output ∧
        SharedNonFixedTranscriptCompatible randomness remaining
  | ⟨.encInverse index output, input⟩ :: remaining =>
      (randomness.2.1.permutation index).symm output = input ∧
        SharedNonFixedTranscriptCompatible randomness remaining
  | ⟨.hash input, output⟩ :: remaining =>
      randomness.2.2 input = output ∧ SharedNonFixedTranscriptCompatible randomness remaining

private theorem permutationTranscriptMatches_cons
    (oracle : PermutationOracle Shared.FixedKeyIndex Block)
    (record : PermutationRecord Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    PermutationTranscriptMatches oracle (record :: history) ↔
      oracle.permutation record.index record.domain = record.range ∧
        PermutationTranscriptMatches oracle history := by
  simp [PermutationTranscriptMatches]

private theorem inverseAnswer_iff (permutation : Equiv.Perm Block) (output input : Block) :
    permutation.symm output = input ↔ permutation input = output := by
  constructor
  · intro equal
    rw [← equal, Equiv.apply_symm_apply]
  · intro equal
    rw [← equal, Equiv.symm_apply_apply]

/-- The actual real handler compatibility is exactly its fixed records and other answers. -/
theorem sharedPublicTranscriptCompatible_iff (randomness : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    OracleTranscriptCompatible (publicHandler id) randomness transcript ↔
      PermutationTranscriptMatches randomness.1 (sharedFixedTranscriptRecords transcript) ∧
        SharedNonFixedTranscriptCompatible randomness transcript := by
  induction transcript with
  | nil => simp [OracleTranscriptCompatible, sharedFixedTranscriptRecords,
      PermutationTranscriptMatches, SharedNonFixedTranscriptCompatible]
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [OracleTranscriptCompatible, Cryptography.publicHandler, Cryptography.publicAnswer, sharedFixedTranscriptRecords,
          SharedNonFixedTranscriptCompatible, inductionHypothesis, permutationTranscriptMatches_cons]
      all_goals try tauto
      case fixedInverse index output =>
        have inverse := inverseAnswer_iff (randomness.1.permutation index) output answer
        tauto

/-- Non-fixed answers do not depend on the shared fixed oracle. -/
theorem sharedNonFixedTranscriptCompatible_fixed
    (first second : PermutationOracle Shared.FixedKeyIndex Block)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    SharedNonFixedTranscriptCompatible (first, enc, hash) transcript ↔
      SharedNonFixedTranscriptCompatible (second, enc, hash) transcript := by
  induction transcript with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [SharedNonFixedTranscriptCompatible, ih]

/-- The fixed projection preserves concatenation of the two adaptive phases. -/
theorem sharedFixedTranscriptRecords_append
    (first second : List (Sigma sharedRealOracleSpec.Answer)) :
    sharedFixedTranscriptRecords (first ++ second) =
      sharedFixedTranscriptRecords first ++ sharedFixedTranscriptRecords second := by
  induction first with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [List.cons_append, sharedFixedTranscriptRecords, ih]

/-- The fixed projection contains at most one record per adversary query. -/
theorem sharedFixedTranscriptRecords_length
    (transcript : List (Sigma sharedRealOracleSpec.Answer)) :
    (sharedFixedTranscriptRecords transcript).length ≤ transcript.length := by
  induction transcript with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [sharedFixedTranscriptRecords, List.length_cons] <;> omega

end
end Kriterion.ArgoMAC.Security
