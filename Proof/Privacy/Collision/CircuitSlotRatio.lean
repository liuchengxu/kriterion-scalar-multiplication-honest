import Proof.Privacy.Programming.ActualGateConstraints
import Proof.Privacy.Transcript.QueryCounts

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype rawInactiveBucketFintype residualFixedQueryDomainFintype

/-- The actual circuit uses one curve gate or 91 point gates in each used slot. -/
def circuitBucketSize (index : Pipeline.FixedKeyIndex) : Nat :=
  match index.kind with
  | .curve _ => 1
  | .point .x .x7 => 0
  | .point .y .y8 => 0
  | .point .y .y10 => 0
  | .point _ _ => FieldMacToECMac.outputMacCount

/-- This map lists exactly the actual gates in a fixed permutation bucket. -/
def circuitBucketGate : (index : Pipeline.FixedKeyIndex) → Fin (circuitBucketSize index) → RawCircuitGate
  | ⟨.curve .x3, bit, _⟩, _ => .inl (0, bit)
  | ⟨.curve .x5, bit, _⟩, _ => .inl (1, bit)
  | ⟨.curve .x7, bit, _⟩, _ => .inl (2, bit)
  | ⟨.curve .y4, bit, _⟩, _ => .inl (3, bit)
  | ⟨.curve .y6, bit, _⟩, _ => .inl (4, bit)
  | ⟨.point .x .y6, bit, _⟩, row => .inr (row, .inl (0, bit))
  | ⟨.point .x .y8, bit, _⟩, row => .inr (row, .inl (1, bit))
  | ⟨.point .x .y10, bit, _⟩, row => .inr (row, .inl (2, bit))
  | ⟨.point .x .x9, bit, _⟩, row => .inr (row, .inl (3, bit))
  | ⟨.point .x .x7, _, _⟩, row => Fin.elim0 row
  | ⟨.point .y .y6, bit, _⟩, row => .inr (row, .inr (.inl (0, bit)))
  | ⟨.point .y .x7, bit, _⟩, row => .inr (row, .inr (.inl (1, bit)))
  | ⟨.point .y .x9, bit, _⟩, row => .inr (row, .inr (.inl (2, bit)))
  | ⟨.point .y .y8, _, _⟩, row => Fin.elim0 row
  | ⟨.point .y .y10, _, _⟩, row => Fin.elim0 row
  | ⟨.point .z .y6, bit, _⟩, row => .inr (row, .inr (.inr (0, bit)))
  | ⟨.point .z .y8, bit, _⟩, row => .inr (row, .inr (.inr (1, bit)))
  | ⟨.point .z .y10, bit, _⟩, row => .inr (row, .inr (.inr (2, bit)))
  | ⟨.point .z .x7, bit, _⟩, row => .inr (row, .inr (.inr (3, bit)))
  | ⟨.point .z .x9, bit, _⟩, row => .inr (row, .inr (.inr (4, bit)))

section CircuitBuckets

variable (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)

/-- This membership proof uses the actual location, bit position, and slot. -/
theorem circuitBucketGate_index (index : Pipeline.FixedKeyIndex) (row : Fin (circuitBucketSize index)) :
    fixedKeyIndex (rawCircuitLocation (circuitBucketGate index row))
      (rawCircuitWindow (circuitBucketGate index row)) index.slot = index := by
  rcases index with ⟨kind, bit, slot⟩
  cases kind with
  | curve adaptor => cases adaptor <;>
      simp [circuitBucketGate, rawCircuitLocation, rawCircuitWindow, fixedKeyIndex, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor <;>
        try exact Fin.elim0 row
      all_goals simp [circuitBucketGate, rawCircuitLocation, rawCircuitWindow, fixedKeyIndex, Pipeline.FixedKeyLocation.kind,
        Nat.mod_eq_of_lt bit.isLt]

/-- This map includes each listed gate in its actual bucket fiber. -/
def circuitBucketUse (index : Pipeline.FixedKeyIndex) (row : Fin (circuitBucketSize index)) :
    RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index :=
  ⟨(circuitBucketGate index row, index.slot), circuitBucketGate_index index row⟩

/-- Each listed bucket use has one distinct output row. -/
theorem circuitBucketUse_injective (index : Pipeline.FixedKeyIndex) :
    Function.Injective (circuitBucketUse keys slopes lifts tables index) := by
  intro first second equal
  have gateEqual := congrArg (fun use => use.1.1) equal
  rcases index with ⟨kind, bit, slot⟩
  cases kind with
  | curve adaptor => exact @Subsingleton.elim (Fin 1) inferInstance first second
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor <;> try exact Fin.elim0 first
      all_goals exact congrArg Prod.fst (Sum.inr.inj gateEqual)

/-- Every actual gate use occurs in this bucket list. -/
theorem circuitBucketUse_surjective (index : Pipeline.FixedKeyIndex) :
    Function.Surjective (circuitBucketUse keys slopes lifts tables index) := by
  rintro ⟨⟨gate, slot⟩, member⟩
  change fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot = index at member
  subst index
  rcases gate with ⟨adaptor, bit⟩ | ⟨row, gate⟩
  · fin_cases adaptor
    all_goals
      refine ⟨⟨0, by simp [circuitBucketSize, fixedKeyIndex, rawCircuitLocation,
        Pipeline.FixedKeyLocation.kind]⟩, ?_⟩
      apply Subtype.ext
      simp [circuitBucketUse, circuitBucketGate, rawCircuitLocation, rawCircuitWindow,
        fixedKeyIndex, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]
  · rcases gate with ⟨adaptor, bit⟩ | (⟨adaptor, bit⟩ | ⟨adaptor, bit⟩) <;> fin_cases adaptor
    all_goals
      refine ⟨row, ?_⟩
      apply Subtype.ext
      simp [circuitBucketUse, circuitBucketGate, rawCircuitLocation, rawCircuitWindow,
        fixedKeyIndex, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]

/-- This equivalence gives the exact size of every actual circuit bucket. -/
def circuitBucketUseEquiv (index : Pipeline.FixedKeyIndex) :
    Fin (circuitBucketSize index) ≃ RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index :=
  Equiv.ofBijective _ ⟨circuitBucketUse_injective keys slopes lifts tables index,
    circuitBucketUse_surjective keys slopes lifts tables index⟩

/-- Every actual bucket has the stated curve, point, or unused size. -/
theorem circuitRawBucketUse_card (index : Pipeline.FixedKeyIndex) :
    Fintype.card (RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index) =
      circuitBucketSize index :=
  (Fintype.card_congr (circuitBucketUseEquiv keys slopes lifts tables index).symm).trans
    (Fintype.card_fin _)

/-- Each actual curve permutation contains exactly one gate assignment. -/
theorem circuitCurveBucket_card (adaptor : Pipeline.CurveAdaptor)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    Fintype.card (RawBucketUse (circuitRawGatePrescription keys slopes lifts tables)
      ⟨.curve adaptor, position, slot⟩) = 1 := by
  rw [circuitRawBucketUse_card]
  rfl

/-- Each used point permutation contains exactly 91 gate assignments. -/
theorem circuitPointBucket_card (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot)
    (used : (coordinate, adaptor) ≠ (.x, .x7) ∧ (coordinate, adaptor) ≠ (.y, .y8) ∧
      (coordinate, adaptor) ≠ (.y, .y10)) :
    Fintype.card (RawBucketUse (circuitRawGatePrescription keys slopes lifts tables)
      ⟨.point coordinate adaptor, position, slot⟩) = 91 := by
  rw [circuitRawBucketUse_card]
  cases coordinate <;> cases adaptor <;>
    simp_all [circuitBucketSize, FieldMacToECMac.outputMacCount]

private theorem outputTweak_injective :
    Function.Injective (fun row : Fin FieldMacToECMac.outputMacCount => BitVec.ofNat 128 row.val) := by
  intro first second equal
  have numeric := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat] at numeric
  have firstBound : first.val < 2 ^ 128 := by have := first.isLt; unfold FieldMacToECMac.outputMacCount at this; omega
  have secondBound : second.val < 2 ^ 128 := by have := second.isLt; unfold FieldMacToECMac.outputMacCount at this; omega
  rw [Nat.mod_eq_of_lt firstBound, Nat.mod_eq_of_lt secondBound] at numeric
  apply Fin.ext
  omega

/-- The actual digit tweak distinguishes all uses of one bucket. -/
theorem circuitRawBucketTweak_injective (index : Pipeline.FixedKeyIndex) :
    Function.Injective (rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index) := by
  have listed : Function.Injective (fun row : Fin (circuitBucketSize index) =>
      (rawCircuitLocation (circuitBucketGate index row)).tweak) := by
    intro first second equal
    rcases index with ⟨kind, bit, slot⟩
    cases kind with
    | curve adaptor => exact @Subsingleton.elim (Fin 1) inferInstance first second
    | point coordinate adaptor =>
        cases coordinate <;> cases adaptor <;> try exact Fin.elim0 first
        all_goals
          apply outputTweak_injective
          simpa [circuitBucketGate, rawCircuitLocation, Pipeline.FixedKeyLocation.tweak] using equal
  intro first second equal
  obtain ⟨a, rfl⟩ := circuitBucketUse_surjective keys slopes lifts tables index first
  obtain ⟨b, rfl⟩ := circuitBucketUse_surjective keys slopes lifts tables index second
  exact congrArg (circuitBucketUse keys slopes lifts tables index) (listed equal)

end CircuitBuckets

/-- No actual permutation bucket contains more than 91 gate uses. -/
theorem circuitBucketSize_le (index : Pipeline.FixedKeyIndex) : circuitBucketSize index ≤ 91 := by
  rcases index with ⟨kind, bit, slot⟩
  cases kind with
  | curve adaptor => norm_num [circuitBucketSize]
  | point coordinate adaptor =>
      cases coordinate <;> cases adaptor <;> norm_num [circuitBucketSize, FieldMacToECMac.outputMacCount]

/-- The whole inactive-label loss fits 182 times the external query count. -/
theorem circuitInactiveLoss_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (selected : RawLabelBucket → Bool) (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index.1) *
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) : Nat) : ℝ≥0∞) /
          Fintype.card Block) ≤ (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞) := by
  classical
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  apply mul_le_mul_left
  simp only [← Nat.cast_sum]
  apply Nat.cast_le.mpr
  calc
    _ ≤ ∑ index : RawInactiveBucket selected,
        182 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) := by
      apply Finset.sum_le_sum
      intro index _
      rw [circuitRawBucketUse_card]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (circuitBucketSize_le index.1))
    _ ≤ ∑ index : Pipeline.FixedKeyIndex,
        182 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Nat.le_add_right _ _).trans_eq (Fintype.sum_subtype_add_sum_subtype
        (fun index => rawSlotBranch index.slot ≠ selected (rawLabelBucket index))
        (fun index => 182 * Fintype.card
          (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index)))
    _ = 182 * ∑ index : Pipeline.FixedKeyIndex,
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 182 * transcript.length := Nat.mul_le_mul_left _ (fixedExternalQueryCount_le transcript)

/-- A declared external query budget bounds the same concrete inactive loss. -/
theorem circuitInactiveLoss_budget_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (selected : RawLabelBucket → Bool) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (queries : Nat) (withinBudget : transcript.length ≤ queries) :
    (∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index.1) *
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) : Nat) : ℝ≥0∞) /
          Fintype.card Block) ≤ (182 * queries : Nat) / (Fintype.card Block : ℝ≥0∞) :=
  (circuitInactiveLoss_le keys slopes lifts tables selected transcript).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 182 withinBudget)) _)

/-- This factor counts the actual gate assignments and residual external queries. -/
def circuitPermutationFactor [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (residual : Pipeline.FixedKeyIndex → Nat) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block - (circuitBucketSize index + residual index)).factorial : ℝ≥0∞) /
    (Fintype.card Block).factorial

/-- This factor assigns independent blocks to gates and keeps the residual query mass. -/
def circuitIndependentFactor [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (residual : Pipeline.FixedKeyIndex → Nat) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹ *
    ((Fintype.card Block - residual index).factorial : ℝ≥0∞) / (Fintype.card Block).factorial

/-- The actual compatible-permutation factor dominates the independent-block factor. -/
theorem circuitIndependentFactor_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (residual : Pipeline.FixedKeyIndex → Nat)
    (fits : ∀ index, circuitBucketSize index + residual index ≤ Fintype.card Block) :
    circuitIndependentFactor residual ≤ circuitPermutationFactor residual := by
  classical
  apply Finset.prod_le_prod'
  intro index _
  exact factorial_ratio_ge_inverse_power (Fintype.card Block) (circuitBucketSize index)
    (residual index) Fintype.card_pos (fits index)

/-- This count removes active replay domains and keeps all inactive query domains. -/
def circuitResidualQueryCount [Fintype Block]
    (gates : RawCircuitGate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Block) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (index : Pipeline.FixedKeyIndex) : Nat :=
  Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
    (rawActiveDomains gates selected publicLabel) index)

section CircuitMass

variable {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (selected : RawLabelBucket → Bool) (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (publicLabel : RawLabelBucket → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index))

include compatible offsetsDistinct referenceActive

/-- The concrete real mass loses at most 182 times the full external query count. -/
theorem circuitSharedInactive_realTranscript_mass_ge :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      circuitPermutationFactor (circuitResidualQueryCount
        (circuitRawGatePrescription keys slopes lifts tables) selected publicLabel transcript) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  have mass := rawSharedInactive_realTranscript_mass_ge
    (circuitRawGatePrescription keys slopes lifts tables) selected wire shift publicLabel randomness transcript
    compatible (circuitRawBucketTweak_injective keys slopes lifts tables) offsetsDistinct referenceActive
  apply le_trans _ mass
  apply mul_le_mul'
  · exact tsub_le_tsub_left (circuitInactiveLoss_le keys slopes lifts tables selected transcript) 1
  · unfold circuitPermutationFactor circuitResidualQueryCount
    simp only [circuitRawBucketUse_card, le_refl]

/-- The same concrete mass bound retains the independent-gate comparison factor. -/
theorem circuitSharedInactive_independentFactor_mass_ge
    (fits : ∀ index, circuitBucketSize index + circuitResidualQueryCount
      (circuitRawGatePrescription keys slopes lifts tables) selected publicLabel transcript index ≤
        Fintype.card Block) :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      circuitIndependentFactor (circuitResidualQueryCount
        (circuitRawGatePrescription keys slopes lifts tables) selected publicLabel transcript) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} :=
  (mul_le_mul_right (circuitIndependentFactor_le _ fits) _).trans
    (circuitSharedInactive_realTranscript_mass_ge keys slopes lifts tables selected wire shift
      publicLabel randomness transcript compatible offsetsDistinct referenceActive)

end CircuitMass

end
end Kriterion.ArgoMAC.Security
