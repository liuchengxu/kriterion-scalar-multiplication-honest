import Proof.Privacy.Source.SharedRawSourceMass
import Proof.Privacy.Source.FullCircuitSourceDensity

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- This type lists the internal roles of one public slot. -/
def SharedSlotRole (slot : Fin 3) := {role : Pipeline.FixedKeySlot // Shared.slotIndex role = slot}

instance sharedSlotRoleFintype (slot : Fin 3) : Fintype (SharedSlotRole slot) := by
  unfold SharedSlotRole
  infer_instance

private theorem legacyIndex_of_shared {legacy : Pipeline.FixedKeyIndex} {index : Shared.FixedKeyIndex}
    (equal : Shared.fixedIndex legacy = index) :
    legacy = ⟨index.kind, index.position, legacy.slot⟩ := by
  cases legacy
  cases index
  cases equal
  rfl

/-- The shared bucket contains the disjoint fibers of its internal roles. -/
def sharedRawBucketRoleEquiv {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Shared.FixedKeyIndex) :
    SharedRawBucketUse gates index ≃
      Σ role : SharedSlotRole index.slot, RawBucketUse gates ⟨index.kind, index.position, role.1⟩ where
  toFun use := ⟨⟨use.1.2, congrArg Shared.FixedKeyIndex.slot use.2⟩,
    ⟨use.1, legacyIndex_of_shared use.2⟩⟩
  invFun use := ⟨use.2.1, by
    rw [use.2.2]
    dsimp only [Shared.fixedIndex]
    rw [use.1.2]⟩
  left_inv use := rfl
  right_inv use := by
    rcases use with ⟨⟨slot, shared⟩, ⟨⟨gate, role⟩, indexed⟩⟩
    have same : role = slot := congrArg Pipeline.FixedKeyIndex.slot indexed
    subst role
    rfl

/-- Slots zero and one contain two roles. Slot two contains one role. -/
theorem sharedSlotRole_card (slot : Fin 3) :
    Fintype.card (SharedSlotRole slot) = if slot.val < 2 then 2 else 1 := by
  fin_cases slot <;> decide

/-- The slot count multiplies each actual curve or point gate count. -/
def sharedCircuitBucketSize (index : Shared.FixedKeyIndex) : Nat :=
  (if index.slot.val < 2 then 2 else 1) *
    circuitBucketSize ⟨index.kind, index.position, .hash 0⟩

/-- This count applies to the exact gate fiber of the three-slot circuit. -/
theorem sharedCircuitBucket_card
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (index : Shared.FixedKeyIndex) :
    Fintype.card (SharedRawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index) =
      sharedCircuitBucketSize index := by
  rw [Fintype.card_congr (sharedRawBucketRoleEquiv _ index), Fintype.card_sigma]
  simp_rw [circuitRawBucketUse_card]
  change (∑ _role : SharedSlotRole index.slot,
    circuitBucketSize ⟨index.kind, index.position, .hash 0⟩) = _
  rw [Finset.sum_const, Finset.card_univ, sharedSlotRole_card, nsmul_eq_mul]
  rfl

/-- A curve bucket contains two assignments in a shared slot and one in the last slot. -/
theorem sharedCurveBucket_size (adaptor : Pipeline.CurveAdaptor)
    (position : Fin coordinateBitCount) (slot : Fin 3) :
    sharedCircuitBucketSize ⟨.curve adaptor, position, slot⟩ = if slot.val < 2 then 2 else 1 := by
  simp only [sharedCircuitBucketSize, circuitBucketSize, Nat.mul_one]

/-- A used point bucket contains 182 assignments in a shared slot and 91 in the last
slot. The adaptor pairs that transmit no row are the three that the row bases drop. -/
theorem sharedPointBucket_size (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (position : Fin coordinateBitCount) (slot : Fin 3)
    (used : (coordinate, adaptor) ≠ (.x, .x7) ∧ (coordinate, adaptor) ≠ (.y, .y8) ∧
      (coordinate, adaptor) ≠ (.y, .y10)) :
    sharedCircuitBucketSize ⟨.point coordinate adaptor, position, slot⟩ =
      if slot.val < 2 then 182 else 91 := by
  cases coordinate <;> cases adaptor <;>
    simp_all [sharedCircuitBucketSize, circuitBucketSize, FieldMacToECMac.outputMacCount]


/-- The shared buckets still contain exactly five role assignments for every gate. -/
theorem sharedCircuitBucketSize_sum :
    ∑ index, sharedCircuitBucketSize index = 5 * Fintype.card RawCircuitGate := by
  let keys : RawCircuitGate → BitAdaptor.Key := fun _ => ⟨0, 0⟩
  let slopes : RawCircuitGate → BaseField := fun _ => 0
  let lifts : RawCircuitGate → FullHashLift := fun _ => 0
  let tables : RawCircuitGate → BitAdaptor.Table := fun _ => defaultBitAdaptorTable
  let gates := circuitRawGatePrescription keys slopes lifts tables
  have counted := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun use : RawCircuitGate × Pipeline.FixedKeySlot => Shared.fixedIndex
      (fixedKeyIndex (gates use.1).location (gates use.1).window use.2)))
  change Fintype.card ((index : Shared.FixedKeyIndex) × SharedRawBucketUse gates index) = _ at counted
  rw [Fintype.card_sigma, Fintype.card_prod] at counted
  have slots : Fintype.card Pipeline.FixedKeySlot = 5 := by decide
  rw [slots] at counted
  dsimp only [gates] at counted
  simp_rw [sharedCircuitBucket_card] at counted
  exact counted.trans (Nat.mul_comm _ _)

set_option maxRecDepth 2048 in
/-- The source density factors over the three actual public slots. -/
theorem sharedFullCircuitSource_uniform_mass [Fintype Block] (source : FullCircuitSource) :
    (PMF.uniformOfFintype FullCircuitSource) source =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block : ENNReal) ^ sharedCircuitBucketSize index)⁻¹ := by
  have sourceCard : Fintype.card FullCircuitSource =
      Fintype.card Block ^ (5 * Fintype.card RawCircuitGate) := by
    convert (@fullCircuitSource_card ‹Fintype Block›) using 1
    exact congrArg (@Fintype.card FullCircuitSource) (Subsingleton.elim _ _)
  rw [PMF.uniformOfFintype_apply, sourceCard, ← sharedCircuitBucketSize_sum, Nat.cast_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  apply ENNReal.prod_inv_distrib
  intro _ _ _ _ _
  exact Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

/-- The actual circuit source has the exact shared-bucket assignment mass. -/
theorem sharedCircuitGarblingMatches_mass [Fintype Block]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (domains : ∀ index, Function.Injective
      (sharedRawBucketDomain (circuitRawGatePrescription keys slopes lifts tables) index))
    (ranges : ∀ index, Function.Injective
      (sharedRawBucketRange (circuitRawGatePrescription keys slopes lifts tables) index)) :
    (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches (circuitRawGatePrescription keys slopes lifts tables)
        (Shared.expandOracle oracle)} =
      ∏ index : Shared.FixedKeyIndex,
        ((Fintype.card Block - sharedCircuitBucketSize index).factorial : ENNReal) /
          (Fintype.card Block).factorial := by
  rw [sharedRawGarblingMatches_mass _ domains ranges]
  simp_rw [sharedCircuitBucket_card]

end
end Kriterion.ArgoMAC.Security
