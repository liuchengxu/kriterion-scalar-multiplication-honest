import Proof.Privacy.Source.SharedLinkedSource
import Proof.Privacy.Collision.SharedPrequeryBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

private theorem hidden_label_eval [Fintype Block] (index : EncPRF.PermutationIndex) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).map (fun hidden => hidden index) =
      PMF.uniformOfFintype Block := by
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween (Equiv.piSplitAt index (fun _ => Block)))
  simpa only [PMF.map_comp, map_uniform_prod_fst, Function.comp_def, Equiv.piSplitAt_apply] using law

private theorem sharedHiddenQuery_mass [Fintype Block]
    (index : EncPRF.PermutationIndex) (shift target : Block) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).toOuterMeasure
      {key | key index ^^^ shift = target} =
        (Fintype.card Block : ENNReal)⁻¹ := by
  have law := congrArg (fun distribution => distribution.map (fun label => label ^^^ shift))
    (hidden_label_eval index)
  have shifted := map_uniformOfFintype_equivBetween (Pipeline.tweakEquiv shift)
  change (PMF.uniformOfFintype Block).map (fun label => label ^^^ shift) = _ at shifted
  rw [PMF.map_comp, shifted] at law
  have mass := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure {target}) law
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at mass
  exact mass

/-- Each query tests both the hash and pad assignments in its actual public bucket. -/
def sharedHiddenQueryCollision
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (sharedCircuitBucketSize (history.get query).index) →
      PrequeryLabelUse) (key : EncPRF.PermutationIndex → Block) : Prop :=
  ∃ query row, key (uses query row).index ^^^
      (uses query row).domainShift = (history.get query).domain ∨
    key (uses query row).index ^^^
      (uses query row).rangeShift = (history.get query).range

/-- A fixed shared-oracle transcript pays at most 364 inverse blocks per query. -/
theorem sharedHiddenQueryCollision_mass_le [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (sharedCircuitBucketSize (history.get query).index) →
      PrequeryLabelUse) :
    (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)).toOuterMeasure
      {key | sharedHiddenQueryCollision history uses key} ≤
        (364 * history.length : Nat) / (Fintype.card Block : ENNReal) := by
  classical
  rw [show {key | sharedHiddenQueryCollision history uses key} =
      ⋃ query, ⋃ row, {key |
        key (uses query row).index ^^^
          (uses query row).domainShift = (history.get query).domain} ∪
        {key | key (uses query row).index ^^^
          (uses query row).rangeShift = (history.get query).range} by
    ext key
    simp only [sharedHiddenQueryCollision, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union]]
  apply (MeasureTheory.measure_iUnion_le _).trans
  rw [tsum_fintype]
  calc
    _ ≤ ∑ query : Fin history.length,
        (2 * sharedCircuitBucketSize (history.get query).index : Nat) /
          (Fintype.card Block : ENNReal) := by
      apply Finset.sum_le_sum
      intro query _
      apply (MeasureTheory.measure_iUnion_le _).trans
      rw [tsum_fintype]
      calc
        _ ≤ ∑ _row : Fin (sharedCircuitBucketSize (history.get query).index),
            2 * (Fintype.card Block : ENNReal)⁻¹ := by
          apply Finset.sum_le_sum
          intro row _
          exact (MeasureTheory.measure_union_le _ _).trans (by
            rw [sharedHiddenQuery_mass, sharedHiddenQuery_mass]
            exact le_of_eq (two_mul _).symm)
        _ = _ := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ ∑ _query : Fin history.length, (364 : ENNReal) / Fintype.card Block := by
      apply Finset.sum_le_sum
      intro query _
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.mul_le_mul_left 2 (sharedCircuitBucketSize_le (history.get query).index)
    _ = _ := by simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]


/-- A good source flag makes every actual raw record fresh in the shared transcript. -/
theorem sharedSourceHiddenQueryCollision_false_fresh
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (context : SharedRetained.Context) (hidden : HiddenPublicSample)
    (labels : EncPRF.PermutationIndex → Block)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (good : ¬ sharedHiddenQueryCollision history
      (sharedSourcePrequeryUses oracle bridgeKey (context.source hidden) (context.lifts hidden) history) labels)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (inactive : rawSlotBranch slot ≠ inputSelectedLabelBit context.input (circuitGateWire gate)) :
    let pointKey := EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) (context.curveKey labels)
    let record := ((sourceGatePrescription (context.source hidden) pointKey (context.curveKey labels) (context.lifts hidden) gate).slotRecord slot)
    FreshPermutationPair history (Shared.fixedIndex record.index) record.domain record.range := by
  dsimp only
  let source := context.source hidden
  let lifts := context.lifts hidden
  let key := context.curveKey labels
  intro prior member sameIndex
  obtain ⟨query, queryEqual⟩ := List.mem_iff_get.mp member
  let use : SharedRawBucketUse
      (circuitRawGatePrescription (fun _ => ⟨0, 0⟩) (circuitSourceSlope source) lifts
        (circuitSourceTable source)) (history.get query).index := ⟨(gate, slot), by
    rw [queryEqual]
    exact sameIndex.symm⟩
  let row := (sharedSourceBucketEquiv source lifts (history.get query).index).symm use
  have selectedUse : sharedSourcePrequeryUses oracle bridgeKey source lifts history query row =
      actualGateLabelUse oracle bridgeKey gate (rawSlotBranch slot)
        (circuitSourceOffset source lifts gate slot) := by
    unfold sharedSourcePrequeryUses row
    rw [Equiv.apply_symm_apply]
  have domainLaw := actualGateLabelUse_domain oracle bridgeKey key gate (rawSlotBranch slot)
    (circuitSourceOffset source lifts gate slot)
  have rangeLaw := actualGateLabelUse_range oracle bridgeKey key gate (rawSlotBranch slot)
    (circuitSourceOffset source lifts gate slot)
  have hiddenLabel : inputKeyLabel key (circuitGateWire gate) (rawSlotBranch slot) =
      labels (circuitGateWire gate) := by
    exact (SharedRetained.curveKey_label context labels _ _).trans (if_neg inactive)
  change inputKeyLabel key (circuitGateWire gate) (rawSlotBranch slot) ^^^ _ = _ at domainLaw rangeLaw
  rw [hiddenLabel] at domainLaw rangeLaw
  constructor
  · intro equal
    apply good
    refine ⟨query, row, Or.inl ?_⟩
    rw [selectedUse]
    change labels (circuitGateWire gate) ^^^ _ = _
    rw [domainLaw, queryEqual]
    cases slot <;> exact equal.symm
  · intro equal
    apply good
    refine ⟨query, row, Or.inr ?_⟩
    rw [selectedUse]
    change labels (circuitGateWire gate) ^^^ _ = _
    rw [rangeLaw, queryEqual]
    cases slot <;> exact equal.symm

end
end Kriterion.ArgoMAC.Security
