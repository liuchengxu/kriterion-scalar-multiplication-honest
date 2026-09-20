import Proof.Privacy.Source.SharedBucketCounts
import Proof.Privacy.Collision.AdaptiveBadBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

private instance sharedPrequeryKeyFinite : Fintype InputMacKey := publicInputMacKeyFintype
private instance sharedPrequeryKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- A public shared bucket contains at most 182 role assignments. -/
theorem sharedCircuitBucketSize_le (index : Shared.FixedKeyIndex) :
    sharedCircuitBucketSize index ≤ 182 := by
  unfold sharedCircuitBucketSize
  have count := circuitBucketSize_le ⟨index.kind, index.position, .hash 0⟩
  split <;> omega

private theorem sharedPrequeryLabel_mass [Fintype Block]
    (index : EncPRF.PermutationIndex) (bit : Bool) (shift target : Block) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | inputKeyLabel key index bit ^^^ shift = target} =
        (Fintype.card Block : ENNReal)⁻¹ := by
  have law := congrArg (fun distribution => distribution.map (fun label => label ^^^ shift))
    (uniform_inputKeyLabel index bit)
  have shifted := map_uniformOfFintype_equivBetween (Pipeline.tweakEquiv shift)
  change (PMF.uniformOfFintype Block).map (fun label => label ^^^ shift) = _ at shifted
  rw [PMF.map_comp, shifted] at law
  have mass := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure {target}) law
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at mass
  exact mass

/-- Each query tests both the hash and pad assignments in its actual public bucket. -/
def sharedPrequeryLabelCollision
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (sharedCircuitBucketSize (history.get query).index) →
      PrequeryLabelUse) (key : InputMacKey) : Prop :=
  ∃ query row, inputKeyLabel key (uses query row).index (uses query row).bit ^^^
      (uses query row).domainShift = (history.get query).domain ∨
    inputKeyLabel key (uses query row).index (uses query row).bit ^^^
      (uses query row).rangeShift = (history.get query).range

/-- A fixed shared-oracle transcript pays at most 364 inverse blocks per query. -/
theorem sharedPrequeryLabelCollision_mass_le [Fintype Block]
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (uses : ∀ query : Fin history.length, Fin (sharedCircuitBucketSize (history.get query).index) →
      PrequeryLabelUse) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedPrequeryLabelCollision history uses key} ≤
        (364 * history.length : Nat) / (Fintype.card Block : ENNReal) := by
  classical
  rw [show {key | sharedPrequeryLabelCollision history uses key} =
      ⋃ query, ⋃ row, {key |
        inputKeyLabel key (uses query row).index (uses query row).bit ^^^
          (uses query row).domainShift = (history.get query).domain} ∪
        {key | inputKeyLabel key (uses query row).index (uses query row).bit ^^^
          (uses query row).rangeShift = (history.get query).range} by
    ext key
    simp only [sharedPrequeryLabelCollision, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union]]
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
            rw [sharedPrequeryLabel_mass, sharedPrequeryLabel_mass]
            exact le_of_eq (two_mul _).symm)
        _ = _ := by simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    _ ≤ ∑ _query : Fin history.length, (364 : ENNReal) / Fintype.card Block := by
      apply Finset.sum_le_sum
      intro query _
      apply ENNReal.div_le_div_right
      exact_mod_cast Nat.mul_le_mul_left 2 (sharedCircuitBucketSize_le (history.get query).index)
    _ = _ := by simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]


/-- This enumeration lists every actual hash or pad use in a shared source bucket. -/
def sharedSourceBucketEquiv (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (index : Shared.FixedKeyIndex) :
    Fin (sharedCircuitBucketSize index) ≃ SharedRawBucketUse
      (circuitRawGatePrescription (fun _ => ⟨0, 0⟩) (circuitSourceSlope source) lifts
        (circuitSourceTable source)) index :=
  (finCongr (sharedCircuitBucket_card (fun _ => ⟨0, 0⟩) (circuitSourceSlope source) lifts
    (circuitSourceTable source) index).symm).trans (Fintype.equivFin _).symm

/-- Each shared transcript use retains the actual linked label and raw source offset. -/
def sharedSourcePrequeryUses (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (query : Fin history.length) (row : Fin (sharedCircuitBucketSize (history.get query).index)) :
    PrequeryLabelUse :=
  let use := sharedSourceBucketEquiv source lifts (history.get query).index row
  actualGateLabelUse oracle bridgeKey use.1.1 (rawSlotBranch use.1.2)
    (circuitSourceOffset source lifts use.1.1 use.1.2)

/-- The actual source uses satisfy the shared query bound. -/
theorem sharedSourcePrequeryCollision_mass_le [Fintype Block]
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | sharedPrequeryLabelCollision history
        (sharedSourcePrequeryUses oracle bridgeKey source lifts history) key} ≤
      (364 * history.length : Nat) / (2 : ENNReal) ^ 128 := by
  have bound := sharedPrequeryLabelCollision_mass_le history
    (sharedSourcePrequeryUses oracle bridgeKey source lifts history)
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  simpa only [card, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- A good source flag makes every actual raw record fresh in the shared transcript. -/
theorem sharedSourcePrequeryCollision_false_fresh
    (oracle : SimulatorOracleCoin) (bridgeKey : BaseField)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block)) (key : InputMacKey)
    (good : ¬ sharedPrequeryLabelCollision history
      (sharedSourcePrequeryUses oracle bridgeKey source lifts history) key)
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot) :
    let pointKey := EncPRF.transformKey oracle.encOracle
      (EncPRF.whiteningKeys oracle.hashOracle bridgeKey) key
    let record := ((sourceGatePrescription source pointKey key lifts gate).slotRecord slot)
    FreshPermutationPair history (Shared.fixedIndex record.index) record.domain record.range := by
  dsimp only
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
  constructor
  · intro equal
    apply good
    refine ⟨query, row, Or.inl ?_⟩
    rw [selectedUse, domainLaw, queryEqual]
    cases slot <;> exact equal.symm
  · intro equal
    apply good
    refine ⟨query, row, Or.inr ?_⟩
    rw [selectedUse, rangeLaw, queryEqual]
    cases slot <;> exact equal.symm

end
end Kriterion.ArgoMAC.Security
