import Proof.Privacy.Collision.SlotCounting
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.Security

open Cryptography
open scoped ENNReal

noncomputable section

private theorem retained_mass_ge {A : Type*} (p : PMF A) (kept : A → Prop)
    (loss : ℝ≥0∞) (badBound : p.toOuterMeasure {a | ¬ kept a} ≤ loss) :
    1 - loss ≤ p.toOuterMeasure {a | kept a} := by
  classical
  have partition : p.toOuterMeasure {a | kept a} + p.toOuterMeasure {a | ¬ kept a} = 1 := by
    simp only [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_add, ← p.tsum_coe]
    exact tsum_congr fun a => by by_cases member : kept a <;> simp [member]
  apply tsub_le_iff_right.mpr
  rw [← partition]
  exact add_le_add_right badBound _

private theorem uniform_prod_eq_bind_fst {A B : Type*}
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) = (PMF.uniformOfFintype A).bind fun a =>
      (PMF.uniformOfFintype B).map fun b => (a, b) := by
  calc
    _ = (PMF.uniformOfFintype (B × A)).map Prod.swap :=
      (map_uniformOfFintype_equivBetween (Equiv.prodComm _ _)).symm
    _ = _ := by
      rw [uniform_prod_eq_bind, PMF.map_bind]
      simp_rw [PMF.map_comp]
      rfl

/-- Adding Q fixed permutation pairs costs at most the independent-block factor. -/
theorem factorial_ratio_ge_inverse_power (N Q q : Nat) (positive : 0 < N)
    (fits : Q + q ≤ N) :
    ((N : ℝ≥0∞) ^ Q)⁻¹ * ((N - q).factorial : ℝ≥0∞) / N.factorial ≤
      ((N - (Q + q)).factorial : ℝ≥0∞) / N.factorial := by
  have natBound : (N - q).factorial ≤ (N - (Q + q)).factorial * N ^ Q := by
    calc
      _ = (N - q - Q).factorial * (N - q).descFactorial Q :=
        (Nat.factorial_mul_descFactorial (by omega)).symm
      _ ≤ (N - q - Q).factorial * N ^ Q :=
        Nat.mul_le_mul_left _ ((Nat.descFactorial_le_pow _ _).trans
          (Nat.pow_le_pow_left (Nat.sub_le _ _) _))
      _ = _ := by rw [Nat.sub_sub, Nat.add_comm q Q]
  apply ENNReal.div_le_div_right
  apply (ENNReal.inv_mul_le_iff (ENNReal.pow_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt positive)) _) (ENNReal.pow_ne_top
      (ENNReal.natCast_ne_top _))).mpr
  exact_mod_cast (natBound.trans_eq (Nat.mul_comm _ _))

/-- Independent uniform coordinates give the product of their event masses. -/
theorem uniformFamily_event_product {Index : Type*} [Fintype Index] [DecidableEq Index]
    {A : Index → Type*} [∀ index, Fintype (A index)] [∀ index, Nonempty (A index)]
    (events : ∀ index, Set (A index)) :
    (PMF.uniformOfFintype (∀ index, A index)).toOuterMeasure
      {values | ∀ index, values index ∈ events index} =
        ∏ index, (PMF.uniformOfFintype (A index)).toOuterMeasure (events index) := by
  classical
  simp only [PMF.toOuterMeasure_uniformOfFintype_apply]
  have count : Fintype.card ({values : ∀ index, A index | ∀ index, values index ∈ events index} :
      Set (∀ index, A index)) =
      ∏ index, Fintype.card (events index) :=
    (Fintype.card_congr Equiv.subtypePiEquivPi).trans Fintype.card_pi
  rw [count, Fintype.card_pi]
  simp only [Nat.cast_prod, div_eq_mul_inv, Finset.prod_mul_distrib]
  rw [ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr (ENNReal.natCast_ne_top _))]

variable {Gate Query : Type*} [Fintype Gate] [Fintype Query] [Fintype Block]

/-- The retained-label mass keeps one excluded gate-query term. -/
theorem retainedSlotLabels_mass_ge (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) :
    1 - ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) / Fintype.card Block ≤
      (PMF.uniformOfFintype Block).toOuterMeasure
        {label | label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange} := by
  classical
  exact retained_mass_ge (PMF.uniformOfFintype Block)
    (fun label => label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange) _
    (by simpa using forbiddenSlotLabels_mass_le tweak offset queryDomain queryRange)

/-- Retained labels contribute their exact compatible-permutation mass. -/
theorem inactiveSlot_exact_mass_ge (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block)
    (tweaksDistinct : Function.Injective tweak) (offsetsDistinct : Function.Injective offset)
    (queryDomainsDistinct : Function.Injective queryDomain)
    (queryRangesDistinct : Function.Injective queryRange) :
    (1 - ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (((Fintype.card Block - (Fintype.card Gate + Fintype.card Query)).factorial : ℝ≥0∞) /
        (Fintype.card Block).factorial) ≤
      (PMF.uniformOfFintype (Block × Equiv.Perm Block)).toOuterMeasure
        {sample | (∀ gate, sample.2 (sample.1 ^^^ tweak gate) = offset gate ^^^ sample.1) ∧
          ∀ query, sample.2 (queryDomain query) = queryRange query} := by
  classical
  apply (mul_le_mul_left (retainedSlotLabels_mass_ge tweak offset queryDomain queryRange) _).trans
  rw [uniform_prod_eq_bind_fst, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro label
  by_cases retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, retained, not_false_eq_true, if_true,
      PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
    rw [retainedSlotAssignment_mass tweak offset queryDomain queryRange label
      tweaksDistinct offsetsDistinct queryDomainsDistinct queryRangesDistinct retained]
  · simp [Set.indicator_apply, retained]

/-- The real inactive-slot mass dominates the independent-gate and query factor. -/
theorem inactiveSlot_mass_ge (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block)
    (tweaksDistinct : Function.Injective tweak) (offsetsDistinct : Function.Injective offset)
    (queryDomainsDistinct : Function.Injective queryDomain)
    (queryRangesDistinct : Function.Injective queryRange)
    (fits : Fintype.card Gate + Fintype.card Query ≤ Fintype.card Block) :
    (1 - ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) / Fintype.card Block) *
      ((Fintype.card Block : ℝ≥0∞) ^ Fintype.card Gate)⁻¹ *
        ((Fintype.card Block - Fintype.card Query).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial ≤
      (PMF.uniformOfFintype (Block × Equiv.Perm Block)).toOuterMeasure
        {sample | (∀ gate, sample.2 (sample.1 ^^^ tweak gate) = offset gate ^^^ sample.1) ∧
          ∀ query, sample.2 (queryDomain query) = queryRange query} := by
  have factorialBound := factorial_ratio_ge_inverse_power (Fintype.card Block)
    (Fintype.card Gate) (Fintype.card Query) Fintype.card_pos fits
  have bound := mul_le_mul_right factorialBound
    (1 - ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) / Fintype.card Block)
  rw [← mul_div_assoc, ← mul_assoc] at bound
  exact bound.trans (inactiveSlot_exact_mass_ge tweak offset queryDomain queryRange
    tweaksDistinct offsetsDistinct queryDomainsDistinct queryRangesDistinct)

/-- The inactive-slot lower bound also holds with ordinary real subtraction. -/
theorem inactiveSlot_mass_ge_real (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block)
    (tweaksDistinct : Function.Injective tweak) (offsetsDistinct : Function.Injective offset)
    (queryDomainsDistinct : Function.Injective queryDomain)
    (queryRangesDistinct : Function.Injective queryRange)
    (fits : Fintype.card Gate + Fintype.card Query ≤ Fintype.card Block) :
    (1 - ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ) / Fintype.card Block) *
      ((Fintype.card Block : ℝ) ^ Fintype.card Gate)⁻¹ *
        ((Fintype.card Block - Fintype.card Query).factorial : ℝ) /
          (Fintype.card Block).factorial ≤
      ((PMF.uniformOfFintype (Block × Equiv.Perm Block)).toOuterMeasure
        {sample | (∀ gate, sample.2 (sample.1 ^^^ tweak gate) = offset gate ^^^ sample.1) ∧
          ∀ query, sample.2 (queryDomain query) = queryRange query}).toReal := by
  classical
  have bound := ENNReal.toReal_mono
    (show (PMF.uniformOfFintype (Block × Equiv.Perm Block)).toOuterMeasure
      {sample | (∀ gate, sample.2 (sample.1 ^^^ tweak gate) = offset gate ^^^ sample.1) ∧
        ∀ query, sample.2 (queryDomain query) = queryRange query} ≠ ⊤ by
      rw [PMF.toOuterMeasure_uniformOfFintype_apply]
      exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (inactiveSlot_mass_ge tweak offset queryDomain queryRange tweaksDistinct offsetsDistinct
      queryDomainsDistinct queryRangesDistinct fits)
  let error : ℝ≥0∞ :=
    ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) / Fintype.card Block
  have subtraction : 1 - error.toReal ≤ (1 - error).toReal := by
    by_cases small : error ≤ 1
    · rw [ENNReal.toReal_sub_of_le small (by simp), ENNReal.toReal_one]
    · have errorFinite : error ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
        (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      have large := ENNReal.toReal_mono errorFinite (le_of_lt (lt_of_not_ge small))
      simp only [ENNReal.toReal_one] at large
      exact (sub_nonpos.mpr large).trans ENNReal.toReal_nonneg
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast] at bound
  apply le_trans ?_ bound
  have subBound := subtraction
  simp only [error, ENNReal.toReal_div, ENNReal.toReal_natCast] at subBound
  gcongr

omit [Fintype Gate] [Fintype Query] [Fintype Block] in
/-- The active-slot permutation factor is at least the independent-block factor. -/
theorem activeSlot_ratio_ge_one (N Q q : Nat) (fits : Q + q ≤ N) :
    1 ≤ (N : ℝ) ^ Q / ((N - q).descFactorial Q : ℝ) := by
  apply (one_le_div (Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr (by omega)))).mpr
  exact_mod_cast (Nat.descFactorial_le_pow (N - q) Q).trans
    (Nat.pow_le_pow_left (Nat.sub_le N q) Q)

section SharedSlots

variable {Wire Slot : Type*} [Fintype Wire] [DecidableEq Wire]
  [Fintype Slot] [DecidableEq Slot] {Gates Queries : Slot → Type*}
  [∀ slot, Fintype (Gates slot)] [∀ slot, Fintype (Queries slot)]
  (wire : Slot → Wire) (shift : Slot → Block)
  (tweak offset : ∀ slot, Gates slot → Block)
  (queryDomain queryRange : ∀ slot, Queries slot → Block)

/-- A retained wire-label tape avoids every slot's query conflicts. -/
def sharedSlotsRetained (labels : Wire → Block) : Prop :=
  ∀ slot, labels (wire slot) ^^^ shift slot ∉
    forbiddenSlotLabels (tweak slot) (offset slot) (queryDomain slot) (queryRange slot)

/-- This event imposes every slot assignment with the shared wire labels. -/
def sharedSlotsCompatible (sample : (Wire → Block) × (Slot → Equiv.Perm Block)) : Prop :=
  ∀ slot,
    (∀ gate, sample.2 slot ((sample.1 (wire slot) ^^^ shift slot) ^^^ tweak slot gate) =
      offset slot gate ^^^ (sample.1 (wire slot) ^^^ shift slot)) ∧
    ∀ query, sample.2 slot (queryDomain slot query) = queryRange slot query

omit [DecidableEq Slot] in
/-- Shared wire labels incur one sum of slot exclusions. -/
theorem sharedSlotsRetained_mass_ge :
    1 - ∑ slot, ((2 * Fintype.card (Gates slot) * Fintype.card (Queries slot) : Nat) : ℝ≥0∞) /
      Fintype.card Block ≤
        (PMF.uniformOfFintype (Wire → Block)).toOuterMeasure
          {labels | sharedSlotsRetained wire shift tweak offset queryDomain queryRange labels} := by
  classical
  apply retained_mass_ge
  have marginal (slot : Slot) :
      (PMF.uniformOfFintype (Wire → Block)).map
        (fun labels => labels (wire slot) ^^^ shift slot) = PMF.uniformOfFintype Block := by
    have evaluation := congrArg (fun p => p.map Prod.fst)
      (map_uniformOfFintype_equivBetween (Equiv.piSplitAt (wire slot) (fun _ => Block)))
    have evaluated : (PMF.uniformOfFintype (Wire → Block)).map
        (fun labels => labels (wire slot)) = PMF.uniformOfFintype Block := by
      simpa only [Equiv.piSplitAt_apply, Function.comp_def, PMF.map_comp, map_uniform_prod_fst] using evaluation
    calc
      _ = ((PMF.uniformOfFintype (Wire → Block)).map
          (fun labels => labels (wire slot))).map (fun label => label ^^^ shift slot) := by
            rw [PMF.map_comp]
            rfl
      _ = _ := by
        rw [evaluated]
        exact map_uniformOfFintype_equivBetween
          ((show Function.Involutive (fun label : Block => label ^^^ shift slot) from
            fun label => by simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]).toPerm)
  rw [show {labels | ¬ sharedSlotsRetained wire shift tweak offset queryDomain queryRange labels} =
      ⋃ slot, {labels | labels (wire slot) ^^^ shift slot ∈
        forbiddenSlotLabels (tweak slot) (offset slot) (queryDomain slot) (queryRange slot)} by
    ext labels
    simp [sharedSlotsRetained]]
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro slot _
  have bound := forbiddenSlotLabels_mass_le (tweak slot) (offset slot)
    (queryDomain slot) (queryRange slot)
  rw [← marginal slot, PMF.toOuterMeasure_map_apply] at bound
  exact bound

omit [Fintype Wire] [DecidableEq Wire] in
/-- A retained shared-label tape gives the product of exact permutation masses. -/
theorem sharedSlotsPermutation_mass (labels : Wire → Block)
    (tweaksDistinct : ∀ slot, Function.Injective (tweak slot))
    (offsetsDistinct : ∀ slot, Function.Injective (offset slot))
    (queryDomainsDistinct : ∀ slot, Function.Injective (queryDomain slot))
    (queryRangesDistinct : ∀ slot, Function.Injective (queryRange slot))
    (retained : sharedSlotsRetained wire shift tweak offset queryDomain queryRange labels) :
    (PMF.uniformOfFintype (Slot → Equiv.Perm Block)).toOuterMeasure
      {permutations | sharedSlotsCompatible wire shift tweak offset queryDomain queryRange
        (labels, permutations)} =
      ∏ slot, ((Fintype.card Block -
        (Fintype.card (Gates slot) + Fintype.card (Queries slot))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial := by
  classical
  refine (uniformFamily_event_product (fun slot => {π : Equiv.Perm Block |
    (∀ gate, π ((labels (wire slot) ^^^ shift slot) ^^^ tweak slot gate) =
      offset slot gate ^^^ (labels (wire slot) ^^^ shift slot)) ∧
    ∀ query, π (queryDomain slot query) = queryRange slot query})).trans ?_
  apply Finset.prod_congr rfl
  intro slot _
  exact retainedSlotAssignment_mass (tweak slot) (offset slot) (queryDomain slot) (queryRange slot)
    (labels (wire slot) ^^^ shift slot) (tweaksDistinct slot) (offsetsDistinct slot)
    (queryDomainsDistinct slot) (queryRangesDistinct slot) (retained slot)

/-- The joint label sum precedes the product over independent permutations. -/
theorem sharedSlots_exact_mass_ge
    (tweaksDistinct : ∀ slot, Function.Injective (tweak slot))
    (offsetsDistinct : ∀ slot, Function.Injective (offset slot))
    (queryDomainsDistinct : ∀ slot, Function.Injective (queryDomain slot))
    (queryRangesDistinct : ∀ slot, Function.Injective (queryRange slot)) :
    (1 - ∑ slot, ((2 * Fintype.card (Gates slot) * Fintype.card (Queries slot) : Nat) : ℝ≥0∞) /
      Fintype.card Block) *
      (∏ slot, ((Fintype.card Block -
        (Fintype.card (Gates slot) + Fintype.card (Queries slot))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial) ≤
      (PMF.uniformOfFintype ((Wire → Block) × (Slot → Equiv.Perm Block))).toOuterMeasure
        {sample | sharedSlotsCompatible wire shift tweak offset queryDomain queryRange sample} := by
  classical
  apply (mul_le_mul_left
    (sharedSlotsRetained_mass_ge wire shift tweak offset queryDomain queryRange) _).trans
  rw [uniform_prod_eq_bind_fst, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro labels
  by_cases retained : sharedSlotsRetained wire shift tweak offset queryDomain queryRange labels
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, retained, if_true,
      PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
    rw [sharedSlotsPermutation_mass wire shift tweak offset queryDomain queryRange labels
      tweaksDistinct offsetsDistinct queryDomainsDistinct queryRangesDistinct retained]
  · simp [Set.indicator_apply, retained]

/-- Shared inactive labels keep one global deficit in the slot product. -/
theorem sharedSlots_mass_ge
    (tweaksDistinct : ∀ slot, Function.Injective (tweak slot))
    (offsetsDistinct : ∀ slot, Function.Injective (offset slot))
    (queryDomainsDistinct : ∀ slot, Function.Injective (queryDomain slot))
    (queryRangesDistinct : ∀ slot, Function.Injective (queryRange slot))
    (fits : ∀ slot, Fintype.card (Gates slot) + Fintype.card (Queries slot) ≤ Fintype.card Block) :
    (1 - ∑ slot, ((2 * Fintype.card (Gates slot) * Fintype.card (Queries slot) : Nat) : ℝ≥0∞) /
      Fintype.card Block) *
      (∏ slot, ((Fintype.card Block : ℝ≥0∞) ^ Fintype.card (Gates slot))⁻¹ *
        ((Fintype.card Block - Fintype.card (Queries slot)).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial) ≤
      (PMF.uniformOfFintype ((Wire → Block) × (Slot → Equiv.Perm Block))).toOuterMeasure
        {sample | sharedSlotsCompatible wire shift tweak offset queryDomain queryRange sample} := by
  have factorBound := Finset.prod_le_prod' (s := (Finset.univ : Finset Slot)) (fun slot _ =>
    factorial_ratio_ge_inverse_power (Fintype.card Block) (Fintype.card (Gates slot))
      (Fintype.card (Queries slot)) Fintype.card_pos (fits slot))
  exact (mul_le_mul_right factorBound _).trans
    (sharedSlots_exact_mass_ge wire shift tweak offset queryDomain queryRange
      tweaksDistinct offsetsDistinct queryDomainsDistinct queryRangesDistinct)

end SharedSlots

end

end Kriterion.ArgoMAC.Security
