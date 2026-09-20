import Proof.Privacy.Source.SharedActiveCounts
import Proof.Privacy.Source.SharedCoveredMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section

/-- The active domain set contains the actual selected source records. -/
def sharedActiveDomains {Gate : Type} (gates : Gate → RawGatePrescription)
    (selected : Shared.FixedKeyIndex → Bool) (index : Shared.FixedKeyIndex) : Set Block :=
  Set.range (fun use : SharedActiveUse gates index (selected index) =>
    sharedRawBucketDomain gates index use.1)

/-- Active replay queries add no constraints to the retained actual source. -/
theorem sharedActiveTranscript_mass [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (selected : Shared.FixedKeyIndex → Bool)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (domains : ∀ index, Function.Injective (sharedRawBucketDomain gates index))
    (ranges : ∀ index, Function.Injective (sharedRawBucketRange gates index))
    (active : ∀ index, ∀ use : SharedActiveUse gates index (selected index),
      reference.permutation index (sharedRawBucketDomain gates index use.1) =
        sharedRawBucketRange gates index use.1)
    (hiddenFresh : ∀ index, ∀ use : SharedRawBucketUse gates index,
      rawSlotBranch use.1.2 ≠ selected index →
      ∀ query : ResidualQueryDomain history (sharedActiveDomains gates selected) index,
        sharedRawBucketDomain gates index use ≠ query.1.1 ∧
        sharedRawBucketRange gates index use ≠ reference.permutation index query.1.1) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧
        PermutationTranscriptMatches oracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (ResidualQueryDomain history (sharedActiveDomains gates selected) index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  apply sharedCoveredTranscript_mass gates reference history (sharedActiveDomains gates selected) compatible
  · rintro index domain ⟨use, equal⟩
    exact ⟨use.1, equal, (active index use).symm.trans (congrArg (reference.permutation index) equal)⟩
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨domains index, Subtype.val_injective.comp Subtype.val_injective, ?_⟩
    intro use query equal
    by_cases chosen : rawSlotBranch use.1.2 = selected index
    · exact query.2 ⟨⟨use, chosen⟩, equal⟩
    · exact (hiddenFresh index use chosen query).1 equal
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨ranges index,
      (reference.permutation index).injective.comp (Subtype.val_injective.comp Subtype.val_injective), ?_⟩
    intro use query equal
    by_cases chosen : rawSlotBranch use.1.2 = selected index
    · have same := (reference.permutation index).injective ((active index ⟨use, chosen⟩).trans equal)
      exact query.2 ⟨⟨use, chosen⟩, same⟩
    · exact (hiddenFresh index use chosen query).2 equal

end
end Kriterion.ArgoMAC.Security
