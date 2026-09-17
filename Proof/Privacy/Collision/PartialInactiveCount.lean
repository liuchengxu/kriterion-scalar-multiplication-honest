import Proof.Privacy.Transcript.AdaptiveGameRatio

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- Each branch uses either its exposed label or its shared hidden label. -/
def partialRawLabels {Wire : Type} (exposed : RawLabelBucket → Bool → Bool)
    (publicLabel : RawLabelBucket → Bool → Block) (wire : RawLabelBucket → Bool → Wire)
    (shift : RawLabelBucket → Bool → Block) (hidden : Wire → Block)
    (bucket : RawLabelBucket) (branch : Bool) : Block :=
  if exposed bucket branch then publicLabel bucket branch
  else hidden (wire bucket branch) ^^^ shift bucket branch

/-- This type keeps every slot whose branch label stays hidden. -/
def PartialInactiveBucket (exposed : RawLabelBucket → Bool → Bool) :=
  {index : Pipeline.FixedKeyIndex // exposed (rawLabelBucket index) (rawSlotBranch index.slot) ≠ true}

local instance partialInactiveBucketFintype [Fintype Pipeline.FixedKeyIndex]
    (exposed : RawLabelBucket → Bool → Bool) : Fintype (PartialInactiveBucket exposed) := by
  classical
  unfold PartialInactiveBucket
  infer_instance

/-- Only exposed branches remove programmed domains from the external query count. -/
def partialActiveDomains {Gate : Type} (gates : Gate → RawGatePrescription)
    (exposed : RawLabelBucket → Bool → Bool) (publicLabel : RawLabelBucket → Bool → Block)
    (index : Pipeline.FixedKeyIndex) : Set Block :=
  if exposed (rawLabelBucket index) (rawSlotBranch index.slot) then
    Set.range (fun use : RawBucketUse gates index =>
      publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use)
  else ∅

section PartialLabels

variable {Gate Wire : Type} [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
  [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
  (gates : Gate → RawGatePrescription) (exposed : RawLabelBucket → Bool → Bool)
  (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
  (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
  (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))

/-- This event retains one hidden-label tape across every inactive slot. -/
def partialRawRetained (hidden : Wire → Block) : Prop :=
  sharedSlotsRetained
    (fun index : PartialInactiveBucket exposed => wire (rawLabelBucket index.1) (rawSlotBranch index.1.slot))
    (fun index => shift (rawLabelBucket index.1) (rawSlotBranch index.1.slot))
    (fun index => rawBucketTweak gates index.1)
    (fun index => rawBucketOffset gates index.1)
    (fun index (query : FixedQueryDomain history index.1) => query.1)
    (fun index (query : FixedQueryDomain history index.1) => reference.permutation index.1 query.1)
    hidden

/-- All hidden branches share one sum of query exclusions. -/
theorem partialRawRetained_mass_ge :
    1 - ∑ index : PartialInactiveBucket exposed,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain history index.1) : Nat) : ℝ≥0∞) / Fintype.card Block ≤
      (PMF.uniformOfFintype (Wire → Block)).toOuterMeasure
        {hidden | partialRawRetained gates exposed wire shift reference history hidden} := by
  classical
  exact sharedSlotsRetained_mass_ge
    (fun index : PartialInactiveBucket exposed => wire (rawLabelBucket index.1) (rawSlotBranch index.1.slot))
    (fun index => shift (rawLabelBucket index.1) (rawSlotBranch index.1.slot))
    (fun index => rawBucketTweak gates index.1)
    (fun index => rawBucketOffset gates index.1)
    (fun index (query : FixedQueryDomain history index.1) => query.1)
    (fun index (query : FixedQueryDomain history index.1) => reference.permutation index.1 query.1)

end PartialLabels

section PartialResidualLabels

variable {Gate Wire : Type} [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
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
      reference.permutation index (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use) =
        rawBucketOffset gates index use ^^^ publicLabel (rawLabelBucket index) (rawSlotBranch index.slot))

include compatible tweaksDistinct offsetsDistinct referenceActive

omit [Fintype Wire] [DecidableEq Wire] in
/-- Active repeated queries use their existing assignment. Inactive slots retain all external queries. -/
theorem partialRawCoveredTranscript_mass (hidden : Wire → Block)
    (kept : partialRawRetained gates exposed wire shift reference history hidden) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches (rawGatesWithLabels gates
        (partialRawLabels exposed publicLabel wire shift hidden)) oracle ∧
          PermutationTranscriptMatches oracle history} =
      ∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history (partialActiveDomains gates exposed publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial := by
  classical
  let labels := partialRawLabels exposed publicLabel wire shift hidden
  let covered := partialActiveDomains gates exposed publicLabel
  have retained : ∀ index, labels (rawLabelBucket index) (rawSlotBranch index.slot) ∉
      forbiddenSlotLabels (rawBucketTweak gates index) (rawBucketOffset gates index)
        (fun query : ResidualFixedQueryDomain history covered index => query.1.1)
        (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1) := by
    intro index
    by_cases active : exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true
    · have domains : ∀ use : RawBucketUse gates index,
          ∀ query : ResidualFixedQueryDomain history covered index,
          publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use ≠ query.1.1 := by
        intro use query equal
        apply query.2
        change query.1.1 ∈ partialActiveDomains gates exposed publicLabel index
        rw [partialActiveDomains, if_pos active]
        exact ⟨use, equal⟩
      apply not_mem_forbidden_of_disjoint
      · intro use query
        simpa only [labels, partialRawLabels, if_pos active] using domains use query
      · intro use query equal
        apply domains use query
        apply (reference.permutation index).injective
        rw [referenceActive index active use]
        simpa only [labels, partialRawLabels, if_pos active] using equal
    · have earlier := kept ⟨index, active⟩
      apply not_mem_forbidden_of_disjoint
      · intro use query
        simpa only [labels, partialRawLabels, if_neg active] using
          slotInput_ne_queryDomain (rawBucketTweak gates index) (rawBucketOffset gates index)
            (fun query : FixedQueryDomain history index => query.1)
            (fun query : FixedQueryDomain history index => reference.permutation index query.1)
            (hidden (wire (rawLabelBucket index) (rawSlotBranch index.slot)) ^^^ shift (rawLabelBucket index) (rawSlotBranch index.slot)) earlier use query.1
      · intro use query
        simpa only [labels, partialRawLabels, if_neg active] using
          slotOutput_ne_queryRange (rawBucketTweak gates index) (rawBucketOffset gates index)
            (fun query : FixedQueryDomain history index => query.1)
            (fun query : FixedQueryDomain history index => reference.permutation index query.1)
            (hidden (wire (rawLabelBucket index) (rawSlotBranch index.slot)) ^^^ shift (rawLabelBucket index) (rawSlotBranch index.slot)) earlier use query.1
  apply rawCoveredFixedTranscript_mass (rawGatesWithLabels gates labels) reference history covered compatible
  · intro index domain member
    change domain ∈ partialActiveDomains gates exposed publicLabel index at member
    by_cases active : exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true
    · rw [partialActiveDomains, if_pos active] at member
      obtain ⟨use, same⟩ := member
      dsimp only at same
      refine ⟨use, ?_, ?_⟩
      · rw [rawGatesWithLabels_domain]
        simpa only [labels, partialRawLabels, if_pos active] using same
      · rw [rawGatesWithLabels_range]
        have assigned := referenceActive index active use
        rw [same] at assigned
        simpa only [labels, partialRawLabels, if_pos active] using assigned.symm
    · simp [partialActiveDomains, active] at member
  · intro index
    rw [rawGatesWithLabels_domain]
    exact retainedSlotDomain_injective (rawBucketTweak gates index) (rawBucketOffset gates index)
      (fun query : ResidualFixedQueryDomain history covered index => query.1.1)
      (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1)
      (labels (rawLabelBucket index) (rawSlotBranch index.slot)) (tweaksDistinct index)
      (Subtype.val_injective.comp Subtype.val_injective) (retained index)
  · intro index
    rw [rawGatesWithLabels_range]
    exact retainedSlotRange_injective (rawBucketTweak gates index) (rawBucketOffset gates index)
      (fun query : ResidualFixedQueryDomain history covered index => query.1.1)
      (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1)
      (labels (rawLabelBucket index) (rawSlotBranch index.slot)) (offsetsDistinct index)
      ((reference.permutation index).injective.comp (Subtype.val_injective.comp Subtype.val_injective))
      (retained index)

/-- The shared inactive-label sum keeps active replay queries in the exact residual count. -/
theorem partialRawShared_residual_mass_ge :
    (1 - ∑ index : PartialInactiveBucket exposed,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain history index.1) : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history (partialActiveDomains gates exposed publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels gates
          (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
            PermutationTranscriptMatches sample.1 history} := by
  classical
  apply (mul_le_mul_left
    (partialRawRetained_mass_ge gates exposed wire shift reference history) _).trans
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro hidden
  by_cases kept : partialRawRetained gates exposed wire shift reference history hidden
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, kept, if_true,
      PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
    rw [partialRawCoveredTranscript_mass gates exposed wire shift reference history publicLabel compatible
      tweaksDistinct offsetsDistinct referenceActive hidden kept]
  · simp [Set.indicator_apply, kept]

end PartialResidualLabels

/-- This bound combines the actual raw garbler view and the actual real handler transcript. -/
theorem partialRawShared_realTranscript_mass_ge {Gate Wire : Type}
    [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (gates : Gate → RawGatePrescription) (exposed : RawLabelBucket → Bool → Bool)
    (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
    (publicLabel : RawLabelBucket → Bool → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (tweaksDistinct : ∀ index, Function.Injective (rawBucketTweak gates index))
    (offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
    (referenceActive : ∀ index, exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse gates index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use) =
            rawBucketOffset gates index use ^^^ publicLabel (rawLabelBucket index) (rawSlotBranch index.slot)) :
    (1 - ∑ index : PartialInactiveBucket exposed,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) : Nat) : ℝ≥0∞) /
          Fintype.card Block) *
      (∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
          (partialActiveDomains gates exposed publicLabel) index))).factorial : ℝ≥0∞) /
            (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels gates
          (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  have fixed := (realOracleTranscriptCompatible_iff randomness transcript).mp compatible
  have event : {sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block) |
      RawGarblingMatches (rawGatesWithLabels gates
        (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} =
      {sample | RawGarblingMatches (rawGatesWithLabels gates
        (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
        PermutationTranscriptMatches sample.1 (fixedOracleTranscriptRecords transcript)} := by
    ext sample
    simp only [Set.mem_setOf_eq, realOracleTranscriptCompatible_iff,
      nonFixedTranscriptCompatible_update, fixed.2, and_true]
  rw [event]
  exact partialRawShared_residual_mass_ge gates exposed wire shift randomness.fixedKeyOracle
    (fixedOracleTranscriptRecords transcript) publicLabel fixed.1 tweaksDistinct offsetsDistinct referenceActive

/-- The whole inactive-label loss fits 182 times the external query count. -/
theorem partialCircuitInactiveLoss_le [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (exposed : RawLabelBucket → Bool → Bool) (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑ index : PartialInactiveBucket exposed,
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
    _ ≤ ∑ index : PartialInactiveBucket exposed,
        182 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) := by
      apply Finset.sum_le_sum
      intro index _
      rw [circuitRawBucketUse_card]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (circuitBucketSize_le index.1))
    _ ≤ ∑ index : Pipeline.FixedKeyIndex,
        182 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Nat.le_add_right _ _).trans_eq (Fintype.sum_subtype_add_sum_subtype
        (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot) ≠ true)
        (fun index => 182 * Fintype.card
          (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index)))
    _ = 182 * ∑ index : Pipeline.FixedKeyIndex,
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 182 * transcript.length := Nat.mul_le_mul_left _ (fixedExternalQueryCount_le transcript)

/-- The corrected circuit factor also holds when both point branches stay hidden. -/
theorem partialCircuit_adaptiveFactor_mass_ge
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (exposed : RawLabelBucket → Bool → Bool)
    (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
    (publicLabel : RawLabelBucket → Bool → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index) (rawSlotBranch index.slot))
    (prior : Pipeline.FixedKeyIndex → Nat)
    (priorFits : ∀ index, circuitBucketSize index + prior index ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index +
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
        (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel)
          index) ≤ Fintype.card Block) :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      adaptiveIdealPermutationFactor (Fintype.card Block) circuitBucketSize prior
        (fun index => Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
          (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel)
            index))
        (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot)) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  have lower := partialRawShared_realTranscript_mass_ge
    (circuitRawGatePrescription keys slopes lifts tables) exposed wire shift publicLabel randomness
    transcript compatible (circuitRawBucketTweak_injective keys slopes lifts tables)
      offsetsDistinct referenceActive
  have loss := tsub_le_tsub_left
    (partialCircuitInactiveLoss_le keys slopes lifts tables exposed transcript) 1
  have factor := adaptiveIdealPermutationFactor_le (Fintype.card Block) circuitBucketSize prior
    (fun index => Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
      (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel)
        index))
    (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot)) Fintype.card_pos
    priorFits residualFits
  apply le_trans _ lower
  apply mul_le_mul' loss
  simpa only [circuitRawBucketUse_card] using factor

/-- A schedule can program only the curve while both point branches stay hidden. -/
theorem partialCircuitProgrammedSource_mass_ratio
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (exposed : RawLabelBucket → Bool → Bool)
    (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
    (publicLabel : RawLabelBucket → Bool → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, exposed (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) (rawSlotBranch index.slot) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            publicLabel (rawLabelBucket index) (rawSlotBranch index.slot))
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries))
    (recordCounts : ∀ index, Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) =
      if exposed (rawLabelBucket index) (rawSlotBranch index.slot) then circuitBucketSize index else 0)
    (residualCounts : ∀ index,
      Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
        (programmedDomains (gateProgramRecords schedule)) index) =
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
        (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel)
          index))
    (priorFits : ∀ index, circuitBucketSize index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index +
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
        (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) exposed publicLabel)
          index) ≤ Fintype.card Block) :
    (1 - (182 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (partialRawLabels exposed publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  rw [programGateSchedule_sourceMass_product state schedule queries fresh reference circuitBucketSize
    (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot)) recordCounts]
  simp_rw [residualCounts]
  exact partialCircuit_adaptiveFactor_mass_ge keys slopes lifts tables exposed wire shift
    publicLabel randomness transcript compatible offsetsDistinct referenceActive _ priorFits residualFits

/-- The invalid branch exposes one curve branch and no point branch. -/
def curveOnlyExposed (selected : RawLabelBucket → Bool) (bucket : RawLabelBucket) (branch : Bool) : Bool :=
  match bucket.1 with
  | .curve _ => decide (branch = selected bucket)
  | .point _ _ => false

/-- A hidden branch retains every external query domain. -/
def partialResidualEquiv_of_hidden {Gate : Type}
    (gates : Gate → RawGatePrescription) (exposed : RawLabelBucket → Bool → Bool)
    (publicLabel : RawLabelBucket → Bool → Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex)
    (hidden : exposed (rawLabelBucket index) (rawSlotBranch index.slot) ≠ true) :
    ResidualFixedQueryDomain history (partialActiveDomains gates exposed publicLabel) index ≃
      FixedQueryDomain history index where
  toFun query := query.1
  invFun query := ⟨query, by
    rw [partialActiveDomains, if_neg hidden]
    exact Set.notMem_empty _⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every point branch keeps its complete external domain count in the invalid experiment. -/
theorem curveOnlyExposed_pointResidual_card [Fintype Block] {Gate : Type}
    (gates : Gate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Bool → Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (position : Fin coordinateBitCount) (slot : Pipeline.FixedKeySlot) :
    Fintype.card (ResidualFixedQueryDomain history
      (partialActiveDomains gates (curveOnlyExposed selected) publicLabel)
        ⟨.point coordinate adaptor, position, slot⟩) =
      Fintype.card (FixedQueryDomain history ⟨.point coordinate adaptor, position, slot⟩) :=
  Fintype.card_congr (partialResidualEquiv_of_hidden gates (curveOnlyExposed selected) publicLabel
    history _ (by change false ≠ true; decide))

/-- The hidden tape keeps the unused curve label and both independent point labels. -/
abbrev IndependentLabelWire := EncPRF.PermutationIndex ⊕ (EncPRF.PermutationIndex × Bool)

/-- This exact split exposes only the selected curve labels. -/
def independentKeyLabelsEquiv (selected : EncPRF.PermutationIndex → Bool) :
    (InputMacKey × InputMacKey) ≃
      ((EncPRF.PermutationIndex → Block) × (IndependentLabelWire → Block)) where
  toFun keys := (fun index => inputKeyLabel keys.1 index (selected index), fun wire =>
    match wire with
    | .inl index => inputKeyLabel keys.1 index (!(selected index))
    | .inr (index, branch) => inputKeyLabel keys.2 index branch)
  invFun sample :=
    (inputKeyLabelEquiv.symm (fun index branch =>
      if branch = selected index then sample.1 index else sample.2 (.inl index)),
      inputKeyLabelEquiv.symm (fun index branch => sample.2 (.inr (index, branch))))
  left_inv keys := by
    apply Prod.ext
    · apply inputKeyLabelEquiv.injective
      rw [Equiv.apply_symm_apply]
      funext index branch
      change (if branch = selected index then inputKeyLabel keys.1 index (selected index)
        else inputKeyLabel keys.1 index (!(selected index))) = inputKeyLabel keys.1 index branch
      cases selected index <;> cases branch <;> rfl
    · exact inputKeyLabelEquiv.symm_apply_apply keys.2
  right_inv sample := by
    apply Prod.ext
    · funext index
      change (inputKeyLabelEquiv (inputKeyLabelEquiv.symm _)) index (selected index) = sample.1 index
      rw [Equiv.apply_symm_apply]
      simp only [if_true]
    · funext wire
      cases wire with
      | inl index =>
          change (inputKeyLabelEquiv (inputKeyLabelEquiv.symm _)) index (!(selected index)) =
            sample.2 (.inl index)
          rw [Equiv.apply_symm_apply]
          cases selected index <;> rfl
      | inr pair =>
          change (inputKeyLabelEquiv (inputKeyLabelEquiv.symm _)) pair.1 pair.2 = sample.2 (.inr pair)
          rw [Equiv.apply_symm_apply]

local instance : Fintype InputMacKey := publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Independent point keys give a uniform hidden-label tape after the exact split. -/
theorem map_uniform_independentKeyLabels [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool) :
    (PMF.uniformOfFintype (InputMacKey × InputMacKey)).map (independentKeyLabelsEquiv selected) =
      PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (IndependentLabelWire → Block)) :=
  map_uniformOfFintype_equivBetween (independentKeyLabelsEquiv selected)

/-- The valid branch exposes selected labels and keeps their unused partners uniform. -/
def selectedKeyLabelsEquiv (selected : EncPRF.PermutationIndex → Bool) :
    InputMacKey ≃ ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block)) where
  toFun key := (fun index => inputKeyLabel key index (selected index),
    fun index => inputKeyLabel key index (!(selected index)))
  invFun sample := inputKeyLabelEquiv.symm (fun index branch =>
    if branch = selected index then sample.1 index else sample.2 index)
  left_inv key := by
    apply inputKeyLabelEquiv.injective
    rw [Equiv.apply_symm_apply]
    funext index branch
    change (if branch = selected index then inputKeyLabel key index (selected index)
      else inputKeyLabel key index (!(selected index))) = inputKeyLabel key index branch
    cases selected index <;> cases branch <;> rfl
  right_inv sample := by
    apply Prod.ext
    · funext index
      change (inputKeyLabelEquiv (inputKeyLabelEquiv.symm _)) index (selected index) = sample.1 index
      rw [Equiv.apply_symm_apply]
      simp only [if_true]
    · funext index
      change (inputKeyLabelEquiv (inputKeyLabelEquiv.symm _)) index (!(selected index)) = sample.2 index
      rw [Equiv.apply_symm_apply]
      cases selected index <;> rfl

/-- The selected-label split preserves the exact uniform source mass. -/
theorem map_uniform_selectedKeyLabels [Fintype Block]
    (selected : EncPRF.PermutationIndex → Bool) :
    (PMF.uniformOfFintype InputMacKey).map (selectedKeyLabelsEquiv selected) =
      PMF.uniformOfFintype ((EncPRF.PermutationIndex → Block) × (EncPRF.PermutationIndex → Block)) :=
  map_uniformOfFintype_equivBetween (selectedKeyLabelsEquiv selected)

end
end Kriterion.ArgoMAC.Security
