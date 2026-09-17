import Proof.Privacy.Collision.PartialInactiveCount
import Proof.Privacy.Source.EncSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- An extra exclusion reduces the retained mass before the extension count. -/
theorem retained_guard_mass_ge {A : Type*} (p : PMF A) (kept guard : A → Prop)
    (loss extra : ℝ≥0∞) (retained : 1 - loss ≤ p.toOuterMeasure {a | kept a})
    (excluded : p.toOuterMeasure {a | ¬ guard a} ≤ extra) :
    1 - (loss + extra) ≤ p.toOuterMeasure {a | kept a ∧ guard a} := by
  have split : p.toOuterMeasure {a | kept a} ≤
      p.toOuterMeasure {a | kept a ∧ guard a} + p.toOuterMeasure {a | ¬ guard a} := by
    simp only [PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro a
    by_cases first : kept a <;> by_cases second : guard a <;> simp [first, second]
  apply tsub_le_iff_right.mpr
  have lower := tsub_le_iff_right.mp (retained.trans (split.trans (add_le_add_right excluded _)))
  simpa only [add_assoc, add_comm extra loss] using lower

/-- The independent hidden tape keeps one full uniform point key. -/
def independentHiddenKeyEquiv : (IndependentLabelWire → Block) ≃
    ((EncPRF.PermutationIndex → Block) × InputMacKey) where
  toFun hidden := (fun index => hidden (.inl index),
    inputKeyLabelEquiv.symm (fun index branch => hidden (.inr (index, branch))))
  invFun pair := fun wire => match wire with
    | .inl index => pair.1 index
    | .inr (index, branch) => inputKeyLabel pair.2 index branch
  left_inv hidden := by
    funext wire
    cases wire with
    | inl index => rfl
    | inr pair => exact congrFun (congrFun (inputKeyLabelEquiv.apply_symm_apply _) pair.1) pair.2
  right_inv pair := by
    apply Prod.ext
    · rfl
    · exact inputKeyLabelEquiv.symm_apply_apply pair.2

/-- Equal Boolean pads are exactly the failure of the source predicate. -/
theorem encSourceGood_iff (source target : InputMacKey) :
    EncSourceGood source target ↔
      ¬ ∃ index, linkingPad source target index false = linkingPad source target index true := by
  simp only [EncSourceGood, not_exists]
  apply forall_congr'
  intro index
  constructor
  · intro injective same
    have := injective same
    cases this
  · intro different first second same
    cases first <;> cases second <;> simp_all

theorem independentHiddenKey_inverse (selected : EncPRF.PermutationIndex → Bool)
    (publicLabels labels : EncPRF.PermutationIndex → Block) (target : InputMacKey) :
    (independentKeyLabelsEquiv selected).symm
      (publicLabels, independentHiddenKeyEquiv.symm (labels, target)) =
      ((selectedKeyLabelsEquiv selected).symm (publicLabels, labels), target) := by
  apply Prod.ext
  · rfl
  · exact inputKeyLabelEquiv.symm_apply_apply target

private theorem uniform_pair_first {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    PMF.uniformOfFintype (A × B) = (PMF.uniformOfFintype A).bind fun a =>
      (PMF.uniformOfFintype B).map fun b => (a, b) := by
  calc
    _ = (PMF.uniformOfFintype (B × A)).map Prod.swap :=
      (map_uniformOfFintype_equivBetween (Equiv.prodComm _ _)).symm
    _ = _ := by
      rw [uniform_prod_eq_bind, PMF.map_bind]
      simp_rw [PMF.map_comp]
      rfl

/-- The concrete hidden tape loses at most 508/N to linking pad collisions. -/
theorem independentHidden_pad_bad_mass_le [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block) :
    (PMF.uniformOfFintype (IndependentLabelWire → Block)).toOuterMeasure
      {hidden | ¬ EncSourceGood
        ((independentKeyLabelsEquiv selected).symm (publicLabels, hidden)).1
        ((independentKeyLabelsEquiv selected).symm (publicLabels, hidden)).2} ≤
      508 / (Fintype.card Block : ℝ≥0∞) := by
  have uniform := map_uniformOfFintype_equivBetween independentHiddenKeyEquiv.symm
  rw [← uniform, PMF.toOuterMeasure_map_apply, uniform_pair_first]
  apply Probability.bind_event_le
  intro labels _
  rw [PMF.toOuterMeasure_map_apply]
  have bound := linkingPad_collision_mass_le
    ((selectedKeyLabelsEquiv selected).symm (publicLabels, labels))
  simpa only [Set.preimage_setOf_eq, independentHiddenKey_inverse,
    encSourceGood_iff, not_not] using bound


/-- The fixed extension count also applies inside an independent label guard. -/
theorem partialRawShared_guard_mass_ge
    {Gate Wire : Type} [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (gates : Gate → RawGatePrescription) (exposed : RawLabelBucket → Bool → Bool)
    (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (publicLabel : RawLabelBucket → Bool → Block)
    (compatible : PermutationTranscriptMatches reference history)
    (tweaksDistinct : ∀ index, Function.Injective (rawBucketTweak gates index))
    (offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
    (referenceActive : ∀ index, exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse gates index,
        reference.permutation index
          (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use) =
            rawBucketOffset gates index use ^^^ publicLabel (rawLabelBucket index) (rawSlotBranch index.slot))
    (guard : (Wire → Block) → Prop) (retainedMass : ℝ≥0∞)
    (retained : retainedMass ≤ (PMF.uniformOfFintype (Wire → Block)).toOuterMeasure
      {hidden | partialRawRetained gates exposed wire shift reference history hidden ∧ guard hidden}) :
    retainedMass *
      (∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history (partialActiveDomains gates exposed publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels gates
          (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
            PermutationTranscriptMatches sample.1 history ∧ guard sample.2} := by
  classical
  apply (mul_le_mul_left retained _).trans
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro hidden
  by_cases kept : partialRawRetained gates exposed wire shift reference history hidden ∧ guard hidden
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, kept, if_true,
      PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq, kept.2, and_true]
    rw [partialRawCoveredTranscript_mass gates exposed wire shift reference history publicLabel compatible
      tweaksDistinct offsetsDistinct referenceActive hidden kept.1]
  · simp [Set.indicator_apply, kept]

/-- The actual independent label tape pays both losses before the fixed count. -/
theorem independentCircuit_guard_mass_ge
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (exposed : RawLabelBucket → Bool → Bool)
    (wire : RawLabelBucket → Bool → IndependentLabelWire) (shift : RawLabelBucket → Bool → Block)
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (publicLabel : RawLabelBucket → Bool → Block)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (compatible : PermutationTranscriptMatches reference (fixedOracleTranscriptRecords transcript))
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        reference.permutation index
          (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index) (rawSlotBranch index.slot)) :
    (1 - ((182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞) +
      508 / (Fintype.card Block : ℝ≥0∞))) *
      (∏ index, ((Fintype.card Block - (circuitBucketSize index +
        Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
          (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (IndependentLabelWire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
          (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
            PermutationTranscriptMatches sample.1 (fixedOracleTranscriptRecords transcript) ∧
            EncSourceGood ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).1
              ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).2} := by
  have retained := partialRawRetained_mass_ge (circuitRawGatePrescription keys slopes lifts tables)
    exposed wire shift reference (fixedOracleTranscriptRecords transcript)
  have loss := tsub_le_tsub_left
    (partialCircuitInactiveLoss_le keys slopes lifts tables exposed transcript) 1
  have joint := retained_guard_mass_ge _ _ _ _ _ (loss.trans retained)
    (independentHidden_pad_bad_mass_le selected publicLabels)
  have bound := partialRawShared_guard_mass_ge
    (circuitRawGatePrescription keys slopes lifts tables) exposed wire shift reference
    (fixedOracleTranscriptRecords transcript) publicLabel compatible
    (circuitRawBucketTweak_injective keys slopes lifts tables) offsetsDistinct referenceActive
    _ _ joint
  simpa only [circuitRawBucketUse_card] using bound

end
end Kriterion.ArgoMAC.Security
