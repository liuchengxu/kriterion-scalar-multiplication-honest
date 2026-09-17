import Proof.Privacy.Programming.Gate
import Cryptography.Permutation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Sum.Basic

namespace Kriterion.ArgoMAC.Security

open Cryptography
open scoped ENNReal

noncomputable section

variable {Gate Query : Type*} [Fintype Gate] [Fintype Query]

/-- This set contains every label that conflicts with a query pair. -/
def forbiddenSlotLabels (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) : Finset Block :=
  Finset.univ.image (fun pair : Gate × Query => queryDomain pair.2 ^^^ tweak pair.1) ∪
    Finset.univ.image (fun pair : Gate × Query => queryRange pair.2 ^^^ offset pair.1)

/-- Each gate-query pair excludes at most two label values. -/
theorem forbiddenSlotLabels_card_le (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) :
    (forbiddenSlotLabels tweak offset queryDomain queryRange).card ≤
      2 * Fintype.card Gate * Fintype.card Query := by
  classical
  unfold forbiddenSlotLabels
  calc
    _ ≤ (Finset.univ.image (fun pair : Gate × Query =>
          queryDomain pair.2 ^^^ tweak pair.1)).card +
        (Finset.univ.image (fun pair : Gate × Query =>
          queryRange pair.2 ^^^ offset pair.1)).card := Finset.card_union_le _ _
    _ ≤ (Finset.univ : Finset (Gate × Query)).card +
        (Finset.univ : Finset (Gate × Query)).card :=
      Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by simp [Fintype.card_prod, two_mul, Nat.add_mul]

/-- A uniform label hits the excluded set with mass at most 2Qq/N. -/
theorem forbiddenSlotLabels_mass_le [Fintype Block] (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) :
    (PMF.uniformOfFintype Block).toOuterMeasure
      {label | label ∈ forbiddenSlotLabels tweak offset queryDomain queryRange} ≤
      ((2 * Fintype.card Gate * Fintype.card Query : Nat) : ℝ≥0∞) /
        Fintype.card Block := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  apply ENNReal.div_le_div_right
  have count : Fintype.card {label //
      label ∈ forbiddenSlotLabels tweak offset queryDomain queryRange} ≤
      2 * Fintype.card Gate * Fintype.card Query :=
    (Fintype.card_of_subtype _ (fun _ => Iff.rfl)).trans_le
      (forbiddenSlotLabels_card_le tweak offset queryDomain queryRange)
  exact_mod_cast count

/-- A shared label avoids the union of all slot exclusions. -/
theorem sharedForbiddenSlotLabels_card_le {Slot : Type*} [Fintype Slot]
    {Gates Queries : Slot → Type*} [∀ slot, Fintype (Gates slot)]
    [∀ slot, Fintype (Queries slot)]
    (tweak offset : ∀ slot, Gates slot → Block)
    (queryDomain queryRange : ∀ slot, Queries slot → Block) :
    (Finset.univ.biUnion fun slot => forbiddenSlotLabels
      (tweak slot) (offset slot) (queryDomain slot) (queryRange slot)).card ≤
      ∑ slot, 2 * Fintype.card (Gates slot) * Fintype.card (Queries slot) := by
  classical
  exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun slot _ =>
    forbiddenSlotLabels_card_le _ _ _ _)

/-- A retained label gives disjoint gate and query inputs. -/
theorem slotInput_ne_queryDomain (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) (label : Block)
    (retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange)
    (gate : Gate) (query : Query) :
    label ^^^ tweak gate ≠ queryDomain query := by
  intro equal
  apply retained
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨(gate, query), Finset.mem_univ _, ?_⟩
  rw [← equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A retained label gives disjoint gate and query outputs. -/
theorem slotOutput_ne_queryRange (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) (label : Block)
    (retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange)
    (gate : Gate) (query : Query) :
    offset gate ^^^ label ≠ queryRange query := by
  intro equal
  apply retained
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨(gate, query), Finset.mem_univ _, ?_⟩
  rw [← equal, BitVec.xor_comm (offset gate) label,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

omit [Fintype Gate] in
/-- Distinct tweaks give distinct gate inputs for every label. -/
theorem slotInput_injective (tweak : Gate → Block)
    (distinct : Function.Injective tweak) (label : Block) :
    Function.Injective (fun gate => label ^^^ tweak gate) := by
  intro first second equal
  exact distinct ((BitVec.xor_right_inj label).mp equal)

omit [Fintype Gate] in
/-- Distinct output offsets give distinct gate outputs for every label. -/
theorem slotOutput_injective (offset : Gate → Block)
    (distinct : Function.Injective offset) (label : Block) :
    Function.Injective (fun gate => offset gate ^^^ label) := by
  intro first second equal
  exact distinct ((BitVec.xor_left_inj label).mp equal)

/-- A retained label preserves input injectivity when query pairs are added. -/
theorem retainedSlotDomain_injective (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) (label : Block)
    (tweaksDistinct : Function.Injective tweak)
    (queriesDistinct : Function.Injective queryDomain)
    (retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange) :
    Function.Injective (Sum.elim (fun gate => label ^^^ tweak gate) queryDomain) :=
  (Sum.elim_injective).mpr ⟨slotInput_injective tweak tweaksDistinct label,
    queriesDistinct, slotInput_ne_queryDomain tweak offset queryDomain queryRange label retained⟩

/-- A retained label preserves output injectivity when query pairs are added. -/
theorem retainedSlotRange_injective (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) (label : Block)
    (offsetsDistinct : Function.Injective offset)
    (queriesDistinct : Function.Injective queryRange)
    (retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange) :
    Function.Injective (Sum.elim (fun gate => offset gate ^^^ label) queryRange) :=
  (Sum.elim_injective).mpr ⟨slotOutput_injective offset offsetsDistinct label,
    queriesDistinct, slotOutput_ne_queryRange tweak offset queryDomain queryRange label retained⟩

/-- The gate implementation has the same input injection as the slot count. -/
theorem gateInput_injective {Index : Type*}
    (location : Index → Pipeline.FixedKeyLocation)
    (distinct : Function.Injective (fun index => (location index).tweak)) (label : Block) :
    Function.Injective (fun index => gateInput (location index) label) := by
  intro first second equal
  apply distinct
  exact (BitVec.xor_right_inj label).mp equal

/-- An injective indexed assignment fixes one permutation pair per index. -/
theorem indexedAssignment_mass {α Index : Type*} [Fintype α] [DecidableEq α]
    [Fintype Index] (domain range : Index → α)
    (domainDistinct : Function.Injective domain) (rangeDistinct : Function.Injective range) :
    (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure
      {permutation | ∀ index, permutation (domain index) = range index} =
      ((Fintype.card α - Fintype.card Index).factorial : ℝ≥0∞) /
        (Fintype.card α).factorial := by
  classical
  letI : Fintype (Set.range domain) := Subtype.fintype _
  let e := Equiv.ofInjective domain domainDistinct
  have event : {permutation : Equiv.Perm α |
      ∀ index, permutation (domain index) = range index} =
      {permutation | ∀ input : Set.range domain,
        permutation input = range (e.symm input)} := by
    ext permutation
    constructor
    · intro compatible input
      have inputEq : domain (e.symm input) = input :=
        congrArg Subtype.val (e.apply_symm_apply input)
      rw [← inputEq]
      exact compatible (e.symm input)
    · intro compatible index
      have assigned := compatible (e index)
      change permutation (domain index) = range (e.symm (e index)) at assigned
      simpa only [e.symm_apply_apply] using assigned
  rw [event]
  have mass := injectiveAssignment_mass (Set.range domain) (range ∘ e.symm)
    (rangeDistinct.comp e.symm.injective)
  exact mass.trans (congrArg
    (fun count : Nat => ((Fintype.card α - count).factorial : ℝ≥0∞) /
      (Fintype.card α).factorial) (Fintype.card_congr e.symm))

/-- Disjoint gate and query assignments fix the sum of their input counts. -/
theorem indexedSumAssignment_mass {α : Type*} [Fintype α] [DecidableEq α]
    (domain range : Gate → α) (queryDomain queryRange : Query → α)
    (domainDistinct : Function.Injective (Sum.elim domain queryDomain))
    (rangeDistinct : Function.Injective (Sum.elim range queryRange)) :
    (PMF.uniformOfFintype (Equiv.Perm α)).toOuterMeasure
      {permutation | (∀ gate, permutation (domain gate) = range gate) ∧
        ∀ query, permutation (queryDomain query) = queryRange query} =
      ((Fintype.card α - (Fintype.card Gate + Fintype.card Query)).factorial : ℝ≥0∞) /
        (Fintype.card α).factorial := by
  have mass := indexedAssignment_mass (Sum.elim domain queryDomain)
    (Sum.elim range queryRange) domainDistinct rangeDistinct
  simpa only [Sum.forall, Sum.elim_inl, Sum.elim_inr, Fintype.card_sum] using mass

/-- Each retained label has the exact permutation-extension mass. -/
theorem retainedSlotAssignment_mass [Fintype Block] (tweak offset : Gate → Block)
    (queryDomain queryRange : Query → Block) (label : Block)
    (tweaksDistinct : Function.Injective tweak) (offsetsDistinct : Function.Injective offset)
    (queryDomainsDistinct : Function.Injective queryDomain)
    (queryRangesDistinct : Function.Injective queryRange)
    (retained : label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange) :
    (PMF.uniformOfFintype (Equiv.Perm Block)).toOuterMeasure
      {permutation | (∀ gate, permutation (label ^^^ tweak gate) = offset gate ^^^ label) ∧
        ∀ query, permutation (queryDomain query) = queryRange query} =
      ((Fintype.card Block - (Fintype.card Gate + Fintype.card Query)).factorial : ℝ≥0∞) /
        (Fintype.card Block).factorial := by
  exact indexedSumAssignment_mass (α := Block) (Gate := Gate) (Query := Query)
      (fun gate => label ^^^ tweak gate) (fun gate => offset gate ^^^ label)
      queryDomain queryRange
      (retainedSlotDomain_injective tweak offset queryDomain queryRange label
        tweaksDistinct queryDomainsDistinct retained)
      (retainedSlotRange_injective tweak offset queryDomain queryRange label
        offsetsDistinct queryRangesDistinct retained)

end

end Kriterion.ArgoMAC.Security
