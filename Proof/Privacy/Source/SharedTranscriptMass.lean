import Proof.Privacy.Source.SharedRawSourceMass
import Proof.Privacy.Distribution.SharedProgrammingDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- This fiber counts each queried domain once in its actual public slot. -/
def SharedQueryDomain (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (index : Shared.FixedKeyIndex) :=
  {domain : Block // ∃ record ∈ history, record.index = index ∧ record.domain = domain}

instance sharedQueryDomainFinite [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) (index : Shared.FixedKeyIndex) :
    Fintype (SharedQueryDomain history index) := by
  classical
  unfold SharedQueryDomain
  infer_instance

/-- A compatible reference fixes every distinct shared query answer. -/
theorem sharedTranscriptMatches_iff_domains
    (reference oracle : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    PermutationTranscriptMatches oracle history ↔
      ∀ index, ∀ query : SharedQueryDomain history index,
        oracle.permutation index query.1 = reference.permutation index query.1 := by
  constructor
  · intro matching index query
    rcases query with ⟨domain, record, member, sameIndex, sameDomain⟩
    subst index
    subst domain
    exact (matching record member).trans (compatible record member).symm
  · intro matching record member
    exact (matching record.index ⟨record.domain, record, member, rfl, rfl⟩).trans
      (compatible record member)

private def sharedTranscriptOracleEquiv :
    PermutationOracle Shared.FixedKeyIndex Block ≃ (Shared.FixedKeyIndex → Equiv.Perm Block) where
  toFun oracle := oracle.permutation
  invFun permutations := ⟨permutations⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every compatible shared transcript has this exact factorial mass. -/
theorem sharedTranscriptMass_eq_product [Fintype Block]
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    Shared.Simulator.transcriptMass history =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - Fintype.card (SharedQueryDomain history index)).factorial : ENNReal) /
          (Fintype.card Block).factorial := by
  have family := uniformFamily_event_product (fun index =>
    {permutation : Equiv.Perm Block | ∀ query : SharedQueryDomain history index,
      permutation query.1 = reference.permutation index query.1})
  have oracleLaw := map_uniformOfFintype_equivBetween sharedTranscriptOracleEquiv
  rw [← oracleLaw, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at family
  dsimp only [sharedTranscriptOracleEquiv, Equiv.coe_fn_mk] at family
  have event : {oracle : PermutationOracle Shared.FixedKeyIndex Block |
      ∀ index, oracle.permutation index ∈ {permutation : Equiv.Perm Block |
        ∀ query : SharedQueryDomain history index,
          permutation query.1 = reference.permutation index query.1}} =
      {oracle | PermutationTranscriptMatches oracle history} := by
    ext oracle
    exact (sharedTranscriptMatches_iff_domains reference oracle history compatible).symm
  rw [event] at family
  unfold Shared.Simulator.transcriptMass
  rw [family]
  apply Finset.prod_congr rfl
  intro index _
  exact indexedAssignment_mass (fun query : SharedQueryDomain history index => query.1)
    (fun query => reference.permutation index query.1) Subtype.val_injective
      ((reference.permutation index).injective.comp Subtype.val_injective)

/-- The real shared source and the external transcript impose one combined assignment. -/
theorem sharedRawGarblingMatches_transcript_mass [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (domains : ∀ index, Function.Injective (Sum.elim (sharedRawBucketDomain gates index)
      (fun query : SharedQueryDomain history index => query.1)))
    (ranges : ∀ index, Function.Injective (Sum.elim (sharedRawBucketRange gates index)
      (fun query : SharedQueryDomain history index => reference.permutation index query.1))) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧
        PermutationTranscriptMatches oracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (SharedQueryDomain history index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  have family := uniformFamily_event_product (fun index =>
    {permutation : Equiv.Perm Block |
      (∀ use : SharedRawBucketUse gates index,
        permutation (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use) ∧
      ∀ query : SharedQueryDomain history index,
        permutation query.1 = reference.permutation index query.1})
  have oracleLaw := map_uniformOfFintype_equivBetween sharedTranscriptOracleEquiv
  rw [← oracleLaw, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] at family
  dsimp only [sharedTranscriptOracleEquiv, Equiv.coe_fn_mk] at family
  have event : {oracle : PermutationOracle Shared.FixedKeyIndex Block |
      ∀ index, oracle.permutation index ∈ {permutation : Equiv.Perm Block |
        (∀ use : SharedRawBucketUse gates index,
          permutation (sharedRawBucketDomain gates index use) = sharedRawBucketRange gates index use) ∧
        ∀ query : SharedQueryDomain history index,
          permutation query.1 = reference.permutation index query.1}} =
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧
        PermutationTranscriptMatches oracle history} := by
    ext oracle
    simp only [Set.mem_setOf_eq, forall_and, sharedRawGarblingMatches_iff,
      sharedTranscriptMatches_iff_domains reference oracle history compatible]
  rw [event] at family
  rw [family]
  apply Finset.prod_congr rfl
  intro index _
  exact indexedSumAssignment_mass (sharedRawBucketDomain gates index) (sharedRawBucketRange gates index)
    (fun query : SharedQueryDomain history index => query.1)
    (fun query => reference.permutation index query.1) (domains index) (ranges index)


/-- Fresh external queries extend the injective actual source assignments. -/
theorem sharedRawGarblingMatches_transcript_mass_of_fresh [Fintype Block] {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (domains : ∀ index, Function.Injective (sharedRawBucketDomain gates index))
    (ranges : ∀ index, Function.Injective (sharedRawBucketRange gates index))
    (fresh : ∀ index, ∀ use : SharedRawBucketUse gates index,
      FreshPermutationPair history index (sharedRawBucketDomain gates index use)
        (sharedRawBucketRange gates index use)) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates (Shared.expandOracle oracle) ∧
        PermutationTranscriptMatches oracle history} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - (Fintype.card (SharedRawBucketUse gates index) +
          Fintype.card (SharedQueryDomain history index))).factorial : ENNReal) /
            (Fintype.card Block).factorial := by
  apply sharedRawGarblingMatches_transcript_mass gates reference history compatible
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨domains index, Subtype.val_injective, ?_⟩
    rintro use ⟨domain, record, member, sameIndex, sameDomain⟩ equal
    exact (fresh index use record member sameIndex).1 (sameDomain.trans equal.symm)
  · intro index
    apply Sum.elim_injective.mpr
    refine ⟨ranges index, (reference.permutation index).injective.comp Subtype.val_injective, ?_⟩
    rintro use ⟨domain, record, member, sameIndex, sameDomain⟩ equal
    have answer : reference.permutation index domain = record.range := by
      rw [← sameIndex, ← sameDomain]
      exact compatible record member
    exact (fresh index use record member sameIndex).2 (answer.symm.trans equal.symm)

end
end Kriterion.ArgoMAC.Security
