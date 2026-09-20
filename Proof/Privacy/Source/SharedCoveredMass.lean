import Proof.Privacy.Source.SharedQueryCounts

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section

private def sharedOracleFamilyEquiv :
    PermutationOracle Shared.FixedKeyIndex Block ≃ (Shared.FixedKeyIndex → Equiv.Perm Block) where
  toFun oracle := oracle.permutation
  invFun permutations := ⟨permutations⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A covered query reuses its source assignment in the actual shared oracle. -/
theorem sharedCoveredTranscript_mass {Gate : Type} [Fintype Gate] [Fintype Block]
    (gates : Gate → RawGatePrescription)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (covered : Shared.FixedKeyIndex → Set Block)
    (compatible : PermutationTranscriptMatches reference history)
    (cover : ∀ index, ∀ domain ∈ covered index, ∃ use : SharedRawBucketUse gates index,
      sharedRawBucketDomain gates index use = domain ∧
        sharedRawBucketRange gates index use = reference.permutation index domain)
    (domainsDistinct : ∀ index, Function.Injective (Sum.elim (sharedRawBucketDomain gates index)
      (fun query : ResidualQueryDomain history covered index => query.1.1)))
    (rangesDistinct : ∀ index, Function.Injective (Sum.elim (sharedRawBucketRange gates index)
      (fun query : ResidualQueryDomain history covered index => reference.permutation index query.1.1))) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧ PermutationTranscriptMatches oracle history} =
      ∏ index, ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
        Fintype.card (ResidualQueryDomain history covered index))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial := by
  classical
  have event : {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧ PermutationTranscriptMatches oracle history} =
      sharedOracleFamilyEquiv ⁻¹' {permutations | ∀ index,
        (∀ use : SharedRawBucketUse gates index,
          permutations index (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use) ∧
        ∀ query : ResidualQueryDomain history covered index,
          permutations index query.1.1 = reference.permutation index query.1.1} := by
    ext oracle
    constructor
    · rintro ⟨garbling, queries⟩ index
      exact ⟨(sharedRawGarblingMatches_iff gates oracle).mp garbling index,
        fun query => (sharedTranscriptMatches_iff_domains reference oracle history compatible).mp
          queries index query.1⟩
    · intro matching
      refine ⟨(sharedRawGarblingMatches_iff gates oracle).mpr (fun index => (matching index).1), ?_⟩
      intro record member
      by_cases overlap : record.domain ∈ covered record.index
      · obtain ⟨use, domain, range⟩ := cover record.index record.domain overlap
        have assigned := (matching record.index).1 use
        change oracle.permutation record.index (sharedRawBucketDomain gates record.index use) =
          sharedRawBucketRange gates record.index use at assigned
        rw [domain, range] at assigned
        exact assigned.trans (compatible record member)
      · exact ((matching record.index).2
          ⟨⟨record.domain, record, member, rfl, rfl⟩, overlap⟩).trans (compatible record member)
  rw [event, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equivBetween sharedOracleFamilyEquiv]
  refine (uniformFamily_event_product (fun index => {permutation : Equiv.Perm Block |
    (∀ use : SharedRawBucketUse gates index,
      permutation (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use) ∧
    ∀ query : ResidualQueryDomain history covered index,
      permutation query.1.1 = reference.permutation index query.1.1})).trans ?_
  apply Finset.prod_congr rfl
  intro index _
  exact indexedSumAssignment_mass (sharedRawBucketDomain gates index) (sharedRawBucketRange gates index)
    (fun query : ResidualQueryDomain history covered index => query.1.1)
    (fun query : ResidualQueryDomain history covered index => reference.permutation index query.1.1)
    (domainsDistinct index) (rangesDistinct index)

end
end Kriterion.ArgoMAC.Security
