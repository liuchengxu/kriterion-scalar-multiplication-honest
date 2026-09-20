import Proof.Privacy.Source.SharedActiveMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section

/-- The invalid-input simulator exposes only curve records. -/
def sharedCurveSlot (index : Shared.FixedKeyIndex) : Bool :=
  match index.kind with
  | .curve _ => true
  | .point _ _ => false

/-- The curve-only schedule leaves every point domain hidden. -/
def sharedCurveDomains {Gate : Type} (gates : Gate → RawGatePrescription)
    (selected : Shared.FixedKeyIndex → Bool) (index : Shared.FixedKeyIndex) : Set Block :=
  if sharedCurveSlot index = true then sharedActiveDomains gates selected index else ∅

/-- The curve-only source counts all point assignments as hidden assignments. -/
theorem sharedCurveTranscript_mass [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (selected : Shared.FixedKeyIndex → Bool)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (domains : ∀ index, Function.Injective (sharedRawBucketDomain gates index))
    (ranges : ∀ index, Function.Injective (sharedRawBucketRange gates index))
    (active : ∀ index, sharedCurveSlot index = true → ∀ use : SharedActiveUse gates index (selected index),
      reference.permutation index (sharedRawBucketDomain gates index use.1) =
        sharedRawBucketRange gates index use.1)
    (hiddenFresh : ∀ index, ∀ use : SharedRawBucketUse gates index,
      ¬ (sharedCurveSlot index = true ∧ rawSlotBranch use.1.2 = selected index) →
      ∀ query : ResidualQueryDomain history (sharedCurveDomains gates selected) index,
        sharedRawBucketDomain gates index use ≠ query.1.1 ∧
        sharedRawBucketRange gates index use ≠ reference.permutation index query.1.1) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧
        PermutationTranscriptMatches oracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (ResidualQueryDomain history (sharedCurveDomains gates selected) index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  apply sharedCoveredTranscript_mass gates reference history (sharedCurveDomains gates selected) compatible
  · intro index domain member
    by_cases curve : sharedCurveSlot index = true
    · rw [sharedCurveDomains, if_pos curve] at member
      obtain ⟨use, equal⟩ := member
      exact ⟨use.1, equal, (active index curve use).symm.trans (congrArg (reference.permutation index) equal)⟩
    · simp only [sharedCurveDomains, curve, Bool.false_eq_true, if_false, Set.mem_empty_iff_false] at member
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨domains index, Subtype.val_injective.comp Subtype.val_injective, ?_⟩
    intro use query equal
    by_cases chosen : sharedCurveSlot index = true ∧ rawSlotBranch use.1.2 = selected index
    · apply query.2
      change query.1.1 ∈ (if sharedCurveSlot index = true then sharedActiveDomains gates selected index else ∅)
      rw [if_pos chosen.1]
      exact ⟨⟨use, chosen.2⟩, equal⟩
    · exact (hiddenFresh index use chosen query).1 equal
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨ranges index,
      (reference.permutation index).injective.comp (Subtype.val_injective.comp Subtype.val_injective), ?_⟩
    intro use query equal
    by_cases chosen : sharedCurveSlot index = true ∧ rawSlotBranch use.1.2 = selected index
    · have same := (reference.permutation index).injective ((active index chosen.1 ⟨use, chosen.2⟩).trans equal)
      apply query.2
      change query.1.1 ∈ (if sharedCurveSlot index = true then sharedActiveDomains gates selected index else ∅)
      rw [if_pos chosen.1]
      exact ⟨⟨use, chosen.2⟩, same⟩
    · exact (hiddenFresh index use chosen query).2 equal

end
end Kriterion.ArgoMAC.Security
