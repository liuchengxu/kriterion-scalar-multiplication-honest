/- This file counts the actual five-slot garbling constraints and public oracle records. -/

import Proof.Privacy.Programming.GarblingConstraints
import Proof.Privacy.Collision.SlotRatio
import Proof.Privacy.Transcript.OracleTranscript

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

/-- This index lists the five curve adaptors and all 92 rows of point adaptors. -/
abbrev RawCircuitGate := (Fin 5 × Fin coordinateBitCount) ⊕
  (Fin FieldMacToECMac.outputMacCount ×
    ((Fin 4 × Fin coordinateBitCount) ⊕ (Fin 3 × Fin coordinateBitCount) ⊕
      (Fin 5 × Fin coordinateBitCount)))

/-- This map uses the actual adaptor order of the mask source. -/
def rawCircuitLocation : RawCircuitGate → Pipeline.FixedKeyLocation
  | .inl (adaptor, _) => .curve (![.x3, .x5, .x7, .y4, .y6] adaptor)
  | .inr (output, .inl (adaptor, _)) =>
      .point output .x (![.y6, .y8, .y10, .x9] adaptor)
  | .inr (output, .inr (.inl (adaptor, _))) =>
      .point output .y (![.y6, .x7, .x9] adaptor)
  | .inr (output, .inr (.inr (adaptor, _))) =>
      .point output .z (![.y6, .y8, .y10, .x7, .x9] adaptor)

def rawCircuitWindow : RawCircuitGate → Nat
  | .inl (_, position) => position.val
  | .inr (_, .inl (_, position)) => position.val
  | .inr (_, .inr (.inl (_, position))) => position.val
  | .inr (_, .inr (.inr (_, position))) => position.val

theorem rawCircuitGate_card : Fintype.card RawCircuitGate = 278638 := by
  simp [RawCircuitGate, coordinateBitCount, FieldMacToECMac.outputMacCount]

/-- This prescription fixes one actual bit-adaptor hash lift and public table. -/
structure RawGatePrescription where
  location : Pipeline.FixedKeyLocation
  window : Nat
  key : BitAdaptor.Key
  slope : BaseField
  lift : FullHashLift
  table : BitAdaptor.Table

/-- This family assigns the prescribed values to every actual circuit position. -/
def circuitRawGatePrescription (keys : RawCircuitGate → BitAdaptor.Key)
    (slopes : RawCircuitGate → BaseField) (lifts : RawCircuitGate → FullHashLift)
    (tables : RawCircuitGate → BitAdaptor.Table) (gate : RawCircuitGate) : RawGatePrescription := {
  location := rawCircuitLocation gate
  window := rawCircuitWindow gate
  key := keys gate
  slope := slopes gate
  lift := lifts gate
  table := tables gate }

/-- This event uses the actual garbler at every prescribed gate. -/
def RawGarblingMatches {Gate : Type} (gates : Gate → RawGatePrescription)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : Prop :=
  ∀ gate, fixedDaviesMeyerHashLift (gates gate).location (gates gate).window
      (gates gate).key.falseLabel oracle = (gates gate).lift ∧
    (BitAdaptor.garble (Pipeline.fixedKeyGate oracle (gates gate).location (gates gate).window)
      (gates gate).slope (gates gate).key).1 = (gates gate).table

def RawGatePrescription.label (gate : RawGatePrescription) : Pipeline.FixedKeySlot → Block
  | .hash _ => gate.key.falseLabel
  | .pad _ => gate.key.trueLabel

def RawGatePrescription.offset (gate : RawGatePrescription) : Pipeline.FixedKeySlot → Block
  | .hash slot => fullHashLiftBlockEquiv gate.lift slot
  | .pad slot => targetPadBlocks gate.table (gate.slope + (gate.lift.val : BaseField)) slot

/-- This fiber lists the actual gate uses in one shared permutation bucket. -/
def RawBucketUse {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Pipeline.FixedKeyIndex) :=
  {use : Gate × Pipeline.FixedKeySlot //
    fixedKeyIndex (gates use.1).location (gates use.1).window use.2 = index}

def rawBucketDomain {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Pipeline.FixedKeyIndex) (use : RawBucketUse gates index) : Block :=
  gateInput (gates use.1.1).location ((gates use.1.1).label use.1.2)

def rawBucketRange {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Pipeline.FixedKeyIndex) (use : RawBucketUse gates index) : Block :=
  (gates use.1.1).offset use.1.2 ^^^
    gateInput (gates use.1.1).location ((gates use.1.1).label use.1.2)

local instance rawBucketUseFintype {Gate : Type} [Fintype Gate]
    (gates : Gate → RawGatePrescription) (index : Pipeline.FixedKeyIndex) :
    Fintype (RawBucketUse gates index) := by
  classical
  unfold RawBucketUse
  infer_instance

/-- The full actual gate view imposes all five constraints in their shared buckets. -/
theorem rawGarblingMatches_iff {Gate : Type} (gates : Gate → RawGatePrescription)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    RawGarblingMatches gates oracle ↔ ∀ index, ∀ use : RawBucketUse gates index,
      oracle.permutation index (rawBucketDomain gates index use) = rawBucketRange gates index use := by
  constructor
  · intro matching index use
    have constraints := (bitAdaptorGarble_eq_iff oracle (gates use.1.1).location
      (gates use.1.1).window (gates use.1.1).key (gates use.1.1).slope
      (gates use.1.1).lift (gates use.1.1).table).mp (matching use.1.1)
    rcases use with ⟨⟨gate, slot⟩, bucket⟩
    subst index
    cases slot with
    | hash slot => exact constraints.1 slot
    | pad slot => exact constraints.2 slot
  · intro matching gate
    apply (bitAdaptorGarble_eq_iff oracle (gates gate).location (gates gate).window
      (gates gate).key (gates gate).slope (gates gate).lift (gates gate).table).mpr
    constructor
    · intro slot
      exact matching _ ⟨(gate, .hash slot), rfl⟩
    · intro slot
      exact matching _ ⟨(gate, .pad slot), rfl⟩

/-- This type counts each queried domain once in its bucket. -/
def FixedQueryDomain (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) :=
  {domain : Block // ∃ record ∈ history, record.index = index ∧ record.domain = domain}

local instance fixedQueryDomainFintype [Fintype Block]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) : Fintype (FixedQueryDomain history index) := by
  classical
  unfold FixedQueryDomain
  infer_instance

/-- A compatible reference fixes the answer at each distinct queried domain. -/
theorem fixedTranscriptMatches_iff_domains
    (reference oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history) :
    PermutationTranscriptMatches oracle history ↔ ∀ index, ∀ query : FixedQueryDomain history index,
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

private def fixedOracleFamilyEquiv :
    PermutationOracle Pipeline.FixedKeyIndex Block ≃ (Pipeline.FixedKeyIndex → Equiv.Perm Block) where
  toFun oracle := oracle.permutation
  invFun permutations := ⟨permutations⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual raw garbler view and all external fixed queries have an exact product mass. -/
theorem rawFixedTranscript_mass {Gate : Type} [Fintype Gate] [Fintype Block]
    [Fintype Pipeline.FixedKeyIndex]
    (gates : Gate → RawGatePrescription)
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (compatible : PermutationTranscriptMatches reference history)
    (domainsDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketDomain gates index)
      (fun query : FixedQueryDomain history index => query.1)))
    (rangesDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketRange gates index)
      (fun query : FixedQueryDomain history index => reference.permutation index query.1))) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates oracle ∧ PermutationTranscriptMatches oracle history} =
      ∏ index, ((Fintype.card Block -
        (Fintype.card (RawBucketUse gates index) + Fintype.card (FixedQueryDomain history index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial := by
  classical
  have event : {oracle | RawGarblingMatches gates oracle ∧ PermutationTranscriptMatches oracle history} =
      fixedOracleFamilyEquiv ⁻¹' {permutations | ∀ index,
        (∀ use : RawBucketUse gates index,
          permutations index (rawBucketDomain gates index use) = rawBucketRange gates index use) ∧
        ∀ query : FixedQueryDomain history index,
          permutations index query.1 = reference.permutation index query.1} := by
    ext oracle
    rw [Set.mem_setOf_eq, rawGarblingMatches_iff,
      fixedTranscriptMatches_iff_domains reference oracle history compatible]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, fixedOracleFamilyEquiv, Equiv.coe_fn_mk, forall_and]
  rw [event, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equivBetween fixedOracleFamilyEquiv]
  refine (uniformFamily_event_product (fun index => {permutation : Equiv.Perm Block |
    (∀ use : RawBucketUse gates index,
      permutation (rawBucketDomain gates index use) = rawBucketRange gates index use) ∧
    ∀ query : FixedQueryDomain history index,
      permutation query.1 = reference.permutation index query.1})).trans ?_
  apply Finset.prod_congr rfl
  intro index _
  exact indexedSumAssignment_mass (rawBucketDomain gates index) (rawBucketRange gates index)
    (fun query : FixedQueryDomain history index => query.1)
    (fun query : FixedQueryDomain history index => reference.permutation index query.1)
    (domainsDistinct index) (rangesDistinct index)

/-- This function extracts both directions of the real fixed-oracle interaction. -/
def fixedOracleTranscriptRecords : List (Sigma Garbling.oracleSpec.Answer) →
    List (PermutationRecord Pipeline.FixedKeyIndex Block)
  | [] => []
  | ⟨.fixedForward index input, output⟩ :: remaining =>
      ⟨.forward, .adversary, index, input, output⟩ :: fixedOracleTranscriptRecords remaining
  | ⟨.fixedInverse index output, input⟩ :: remaining =>
      ⟨.inverse, .adversary, index, input, output⟩ :: fixedOracleTranscriptRecords remaining
  | ⟨.encForward _ _, _⟩ :: remaining => fixedOracleTranscriptRecords remaining
  | ⟨.encInverse _ _, _⟩ :: remaining => fixedOracleTranscriptRecords remaining
  | ⟨.hash _, _⟩ :: remaining => fixedOracleTranscriptRecords remaining

/-- This condition fixes the other actual oracle answers while the fixed family varies. -/
def NonFixedTranscriptCompatible (randomness : Garbling.Randomness) :
    List (Sigma Garbling.oracleSpec.Answer) → Prop
  | [] => True
  | ⟨.fixedForward _ _, _⟩ :: remaining => NonFixedTranscriptCompatible randomness remaining
  | ⟨.fixedInverse _ _, _⟩ :: remaining => NonFixedTranscriptCompatible randomness remaining
  | ⟨.encForward index input, output⟩ :: remaining =>
      randomness.encPRFOracle.permutation index input = output ∧
        NonFixedTranscriptCompatible randomness remaining
  | ⟨.encInverse index output, input⟩ :: remaining =>
      (randomness.encPRFOracle.permutation index).symm output = input ∧
        NonFixedTranscriptCompatible randomness remaining
  | ⟨.hash input, output⟩ :: remaining =>
      randomness.hashOracle input = output ∧ NonFixedTranscriptCompatible randomness remaining

private theorem permutationTranscriptMatches_cons
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) :
    PermutationTranscriptMatches oracle (record :: history) ↔
      oracle.permutation record.index record.domain = record.range ∧
        PermutationTranscriptMatches oracle history := by
  simp [PermutationTranscriptMatches]

private theorem inverseAnswer_iff (permutation : Equiv.Perm Block) (output input : Block) :
    permutation.symm output = input ↔ permutation input = output := by
  constructor
  · intro equal
    rw [← equal, Equiv.apply_symm_apply]
  · intro equal
    rw [← equal, Equiv.symm_apply_apply]

/-- The actual real handler compatibility is exactly its fixed records and other answers. -/
theorem realOracleTranscriptCompatible_iff (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    OracleTranscriptCompatible Garbling.oracleHandler randomness transcript ↔
      PermutationTranscriptMatches randomness.fixedKeyOracle (fixedOracleTranscriptRecords transcript) ∧
        NonFixedTranscriptCompatible randomness transcript := by
  induction transcript with
  | nil => simp [OracleTranscriptCompatible, fixedOracleTranscriptRecords,
      PermutationTranscriptMatches, NonFixedTranscriptCompatible]
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [OracleTranscriptCompatible, Garbling.oracleHandler, Cryptography.publicHandler, Cryptography.publicAnswer, fixedOracleTranscriptRecords,
          NonFixedTranscriptCompatible, inductionHypothesis, permutationTranscriptMatches_cons]
      all_goals try tauto
      case fixedInverse index output =>
        have inverse := inverseAnswer_iff (randomness.fixedKeyOracle.permutation index) output answer
        tauto

@[simp] theorem nonFixedTranscriptCompatible_update (randomness : Garbling.Randomness)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    NonFixedTranscriptCompatible {randomness with fixedKeyOracle := oracle} transcript ↔
      NonFixedTranscriptCompatible randomness transcript := by
  induction transcript with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;> simp only [NonFixedTranscriptCompatible, inductionHypothesis]

/-- This exact mass uses the actual garbler view and the actual real oracle handler. -/
theorem rawRealOracleTranscript_mass {Gate : Type} [Fintype Gate] [Fintype Block]
    [Fintype Pipeline.FixedKeyIndex]
    (gates : Gate → RawGatePrescription) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (domainsDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketDomain gates index)
      (fun query : FixedQueryDomain (fixedOracleTranscriptRecords transcript) index => query.1)))
    (rangesDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketRange gates index)
      (fun query : FixedQueryDomain (fixedOracleTranscriptRecords transcript) index =>
        randomness.fixedKeyOracle.permutation index query.1))) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates oracle ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := oracle} transcript} =
      ∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial := by
  have fixed := (realOracleTranscriptCompatible_iff randomness transcript).mp compatible
  have event : {oracle | RawGarblingMatches gates oracle ∧
      OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with fixedKeyOracle := oracle} transcript} =
      {oracle | RawGarblingMatches gates oracle ∧
        PermutationTranscriptMatches oracle (fixedOracleTranscriptRecords transcript)} := by
    ext oracle
    simp only [Set.mem_setOf_eq, realOracleTranscriptCompatible_iff,
      nonFixedTranscriptCompatible_update, fixed.2, and_true]
  rw [event]
  exact rawFixedTranscript_mass gates randomness.fixedKeyOracle _ fixed.1 domainsDistinct rangesDistinct

/-- This prescription uses the actual 92 digit tweaks in one point adaptor. -/
def pointRawGatePrescription (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (window : Nat) (key : BitAdaptor.Key)
    (slopes : Fin FieldMacToECMac.outputMacCount → BaseField)
    (lifts : Fin FieldMacToECMac.outputMacCount → FullHashLift)
    (tables : Fin FieldMacToECMac.outputMacCount → BitAdaptor.Table)
    (output : Fin FieldMacToECMac.outputMacCount) : RawGatePrescription := {
  location := .point output coordinate adaptor
  window := window
  key := key
  slope := slopes output
  lift := lifts output
  table := tables output }

/-- Each of the five point permutations receives exactly one use per output digit. -/
def pointRawBucketUseEquiv (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (window : Nat) (key : BitAdaptor.Key)
    (slopes : Fin FieldMacToECMac.outputMacCount → BaseField)
    (lifts : Fin FieldMacToECMac.outputMacCount → FullHashLift)
    (tables : Fin FieldMacToECMac.outputMacCount → BitAdaptor.Table)
    (slot : Pipeline.FixedKeySlot) :
    RawBucketUse (pointRawGatePrescription coordinate adaptor window key slopes lifts tables)
      (fixedKeyIndex (.point ⟨0, by decide⟩ coordinate adaptor) window slot) ≃ Fin FieldMacToECMac.outputMacCount where
  toFun use := use.1.1
  invFun output := ⟨(output, slot), rfl⟩
  left_inv use := by
    rcases use with ⟨⟨output, actualSlot⟩, bucket⟩
    have sameSlot : actualSlot = slot := congrArg Pipeline.FixedKeyIndex.slot bucket
    subst actualSlot
    rfl
  right_inv _ := rfl

/-- The actual shared bucket contains 91 gate constraints in each hash or pad permutation. -/
theorem pointRawBucketUse_card (coordinate : Pipeline.PointCoordinate) (adaptor : Pipeline.PointAdaptor)
    (window : Nat) (key : BitAdaptor.Key)
    (slopes : Fin FieldMacToECMac.outputMacCount → BaseField)
    (lifts : Fin FieldMacToECMac.outputMacCount → FullHashLift)
    (tables : Fin FieldMacToECMac.outputMacCount → BitAdaptor.Table)
    (slot : Pipeline.FixedKeySlot) :
    Fintype.card (RawBucketUse (pointRawGatePrescription coordinate adaptor window key slopes lifts tables)
      (fixedKeyIndex (.point ⟨0, by decide⟩ coordinate adaptor) window slot)) = 91 :=
  (Fintype.card_congr (pointRawBucketUseEquiv coordinate adaptor window key slopes lifts tables slot)).trans
    (Fintype.card_fin _)

/-- This index identifies the label pair shared by the five slot permutations. -/
abbrev RawLabelBucket := Pipeline.FixedKeyKind × Fin coordinateBitCount

def rawLabelBucket (index : Pipeline.FixedKeyIndex) : RawLabelBucket := (index.kind, index.position)

def rawSlotBranch : Pipeline.FixedKeySlot → Bool
  | .hash _ => false
  | .pad _ => true

/-- This function changes only the shared gate labels. -/
def rawGatesWithLabels {Gate : Type} (gates : Gate → RawGatePrescription)
    (labels : RawLabelBucket → Bool → Block) (gate : Gate) : RawGatePrescription :=
  let bucket := rawLabelBucket (fixedKeyIndex (gates gate).location (gates gate).window (.hash 0))
  { gates gate with key := { falseLabel := labels bucket false, trueLabel := labels bucket true } }

def rawBucketTweak {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Pipeline.FixedKeyIndex) (use : RawBucketUse gates index) : Block :=
  (gates use.1.1).location.tweak

def rawBucketOffset {Gate : Type} (gates : Gate → RawGatePrescription)
    (index : Pipeline.FixedKeyIndex) (use : RawBucketUse gates index) : Block :=
  (gates use.1.1).offset use.1.2 ^^^ (gates use.1.1).location.tweak

theorem rawGatesWithLabels_domain {Gate : Type} (gates : Gate → RawGatePrescription)
    (labels : RawLabelBucket → Bool → Block) (index : Pipeline.FixedKeyIndex) :
    rawBucketDomain (rawGatesWithLabels gates labels) index =
      fun use : RawBucketUse gates index =>
        labels (rawLabelBucket index) (rawSlotBranch index.slot) ^^^ rawBucketTweak gates index use := by
  funext use
  rcases use with ⟨⟨gate, slot⟩, bucket⟩
  subst index
  cases slot <;> rfl

theorem rawGatesWithLabels_range {Gate : Type} (gates : Gate → RawGatePrescription)
    (labels : RawLabelBucket → Bool → Block) (index : Pipeline.FixedKeyIndex) :
    rawBucketRange (rawGatesWithLabels gates labels) index =
      fun use : RawBucketUse gates index => rawBucketOffset gates index use ^^^
        labels (rawLabelBucket index) (rawSlotBranch index.slot) := by
  funext use
  rcases use with ⟨⟨gate, slot⟩, bucket⟩
  subst index
  cases slot <;>
    simp [rawBucketRange, rawBucketOffset, rawGatesWithLabels, RawGatePrescription.offset,
      RawGatePrescription.label, gateInput, rawLabelBucket, fixedKeyIndex, rawSlotBranch,
      BitVec.xor_assoc, BitVec.xor_comm] <;>
    rw [← BitVec.xor_assoc, BitVec.xor_comm (gates gate).location.tweak, BitVec.xor_assoc]

/-- The selected branch uses its public label. The other branch uses one shared hidden label. -/
def rawMixedLabels {Wire : Type} (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Block) (wire : RawLabelBucket → Wire)
    (shift : RawLabelBucket → Block) (hidden : Wire → Block)
    (bucket : RawLabelBucket) (branch : Bool) : Block :=
  if branch = selected bucket then publicLabel bucket else hidden (wire bucket) ^^^ shift bucket

/-- This type contains only the slot permutations for the hidden branch. -/
def RawInactiveBucket (selected : RawLabelBucket → Bool) :=
  {index : Pipeline.FixedKeyIndex // rawSlotBranch index.slot ≠ selected (rawLabelBucket index)}

local instance rawInactiveBucketFintype [Fintype Pipeline.FixedKeyIndex]
    (selected : RawLabelBucket → Bool) : Fintype (RawInactiveBucket selected) := by
  classical
  unfold RawInactiveBucket
  infer_instance

section MixedLabels

variable {Gate Wire : Type} [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
  [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
  (gates : Gate → RawGatePrescription) (selected : RawLabelBucket → Bool)
  (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
  (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
  (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))

/-- This event retains one hidden-label tape across every inactive slot. -/
def rawInactiveRetained (hidden : Wire → Block) : Prop :=
  sharedSlotsRetained
    (fun index : RawInactiveBucket selected => wire (rawLabelBucket index.1))
    (fun index => shift (rawLabelBucket index.1))
    (fun index => rawBucketTweak gates index.1)
    (fun index => rawBucketOffset gates index.1)
    (fun index (query : FixedQueryDomain history index.1) => query.1)
    (fun index (query : FixedQueryDomain history index.1) => reference.permutation index.1 query.1)
    hidden

/-- Shared hidden labels lose one sum over inactive slot exclusions. -/
theorem rawInactiveRetained_mass_ge :
    1 - ∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain history index.1) : Nat) : ℝ≥0∞) / Fintype.card Block ≤
      (PMF.uniformOfFintype (Wire → Block)).toOuterMeasure
        {hidden | rawInactiveRetained gates selected wire shift reference history hidden} := by
  classical
  exact sharedSlotsRetained_mass_ge
    (fun index : RawInactiveBucket selected => wire (rawLabelBucket index.1))
    (fun index => shift (rawLabelBucket index.1))
    (fun index => rawBucketTweak gates index.1)
    (fun index => rawBucketOffset gates index.1)
    (fun index (query : FixedQueryDomain history index.1) => query.1)
    (fun index (query : FixedQueryDomain history index.1) => reference.permutation index.1 query.1)

end MixedLabels

/-- This type omits external queries whose domains already have a selected assignment. -/
def ResidualFixedQueryDomain
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (covered : Pipeline.FixedKeyIndex → Set Block) (index : Pipeline.FixedKeyIndex) :=
  {query : FixedQueryDomain history index // query.1 ∉ covered index}

local instance residualFixedQueryDomainFintype [Fintype Block]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (covered : Pipeline.FixedKeyIndex → Set Block) (index : Pipeline.FixedKeyIndex) :
    Fintype (ResidualFixedQueryDomain history covered index) := by
  classical
  unfold ResidualFixedQueryDomain
  infer_instance

/-- Consistent covered queries add no new permutation constraint. -/
theorem rawCoveredFixedTranscript_mass {Gate : Type} [Fintype Gate] [Fintype Block]
    [Fintype Pipeline.FixedKeyIndex] (gates : Gate → RawGatePrescription)
    (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (covered : Pipeline.FixedKeyIndex → Set Block)
    (compatible : PermutationTranscriptMatches reference history)
    (cover : ∀ index, ∀ domain ∈ covered index, ∃ use : RawBucketUse gates index,
      rawBucketDomain gates index use = domain ∧
        rawBucketRange gates index use = reference.permutation index domain)
    (domainsDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketDomain gates index)
      (fun query : ResidualFixedQueryDomain history covered index => query.1.1)))
    (rangesDistinct : ∀ index, Function.Injective (Sum.elim (rawBucketRange gates index)
      (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1))) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches gates oracle ∧ PermutationTranscriptMatches oracle history} =
      ∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history covered index))).factorial : ℝ≥0∞) /
          (Fintype.card Block).factorial := by
  classical
  have event : {oracle | RawGarblingMatches gates oracle ∧ PermutationTranscriptMatches oracle history} =
      fixedOracleFamilyEquiv ⁻¹' {permutations | ∀ index,
        (∀ use : RawBucketUse gates index,
          permutations index (rawBucketDomain gates index use) = rawBucketRange gates index use) ∧
        ∀ query : ResidualFixedQueryDomain history covered index,
          permutations index query.1.1 = reference.permutation index query.1.1} := by
    ext oracle
    constructor
    · rintro ⟨garbling, queries⟩ index
      exact ⟨(rawGarblingMatches_iff gates oracle).mp garbling index,
        fun query => (fixedTranscriptMatches_iff_domains reference oracle history compatible).mp
          queries index query.1⟩
    · intro matching
      refine ⟨(rawGarblingMatches_iff gates oracle).mpr (fun index => (matching index).1), ?_⟩
      intro record member
      by_cases overlap : record.domain ∈ covered record.index
      · obtain ⟨use, domain, range⟩ := cover record.index record.domain overlap
        have assigned := (matching record.index).1 use
        change oracle.permutation record.index (rawBucketDomain gates record.index use) =
          rawBucketRange gates record.index use at assigned
        rw [domain, range] at assigned
        exact assigned.trans (compatible record member)
      · exact ((matching record.index).2
          ⟨⟨record.domain, record, member, rfl, rfl⟩, overlap⟩).trans (compatible record member)
  rw [event, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equivBetween fixedOracleFamilyEquiv]
  refine (uniformFamily_event_product (fun index => {permutation : Equiv.Perm Block |
    (∀ use : RawBucketUse gates index,
      permutation (rawBucketDomain gates index use) = rawBucketRange gates index use) ∧
    ∀ query : ResidualFixedQueryDomain history covered index,
      permutation query.1.1 = reference.permutation index query.1.1})).trans ?_
  apply Finset.prod_congr rfl
  intro index _
  exact indexedSumAssignment_mass (rawBucketDomain gates index) (rawBucketRange gates index)
    (fun query : ResidualFixedQueryDomain history covered index => query.1.1)
    (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1)
    (domainsDistinct index) (rangesDistinct index)

theorem not_mem_forbidden_of_disjoint {Gate Query : Type} [Fintype Gate] [Fintype Query]
    (tweak offset : Gate → Block) (queryDomain queryRange : Query → Block) (label : Block)
    (domains : ∀ gate query, label ^^^ tweak gate ≠ queryDomain query)
    (ranges : ∀ gate query, offset gate ^^^ label ≠ queryRange query) :
    label ∉ forbiddenSlotLabels tweak offset queryDomain queryRange := by
  classical
  intro member
  rcases Finset.mem_union.mp member with domain | range
  · obtain ⟨⟨gate, query⟩, _, equal⟩ := Finset.mem_image.mp domain
    apply domains gate query
    rw [← equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · obtain ⟨⟨gate, query⟩, _, equal⟩ := Finset.mem_image.mp range
    apply ranges gate query
    rw [← equal, BitVec.xor_comm (offset gate), BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]

/-- Only active gate inputs remove repeated external queries from the count. -/
def rawActiveDomains {Gate : Type} (gates : Gate → RawGatePrescription)
    (selected : RawLabelBucket → Bool) (publicLabel : RawLabelBucket → Block)
    (index : Pipeline.FixedKeyIndex) : Set Block :=
  if rawSlotBranch index.slot = selected (rawLabelBucket index) then
    Set.range (fun use : RawBucketUse gates index =>
      publicLabel (rawLabelBucket index) ^^^ rawBucketTweak gates index use)
  else ∅

/-- Inactive slots retain every external queried domain. -/
def residualFixedQueryDomainEquiv_of_inactive {Gate : Type}
    (gates : Gate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Block) (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex)
    (inactive : rawSlotBranch index.slot ≠ selected (rawLabelBucket index)) :
    ResidualFixedQueryDomain history (rawActiveDomains gates selected publicLabel) index ≃
      FixedQueryDomain history index where
  toFun query := query.1
  invFun query := ⟨query, by simp [rawActiveDomains, inactive]⟩
  left_inv _ := rfl
  right_inv _ := rfl

section ResidualLabels

variable {Gate Wire : Type} [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
  [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
  (gates : Gate → RawGatePrescription) (selected : RawLabelBucket → Bool)
  (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
  (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
  (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
  (publicLabel : RawLabelBucket → Block)
  (compatible : PermutationTranscriptMatches reference history)
  (tweaksDistinct : ∀ index, Function.Injective (rawBucketTweak gates index))
  (offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
  (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
    ∀ use : RawBucketUse gates index,
      reference.permutation index (publicLabel (rawLabelBucket index) ^^^ rawBucketTweak gates index use) =
        rawBucketOffset gates index use ^^^ publicLabel (rawLabelBucket index))

include compatible tweaksDistinct offsetsDistinct referenceActive

omit [Fintype Wire] [DecidableEq Wire] in
/-- Active repeated queries use their existing assignment. Inactive slots retain all external queries. -/
theorem rawMixedCoveredTranscript_mass (hidden : Wire → Block)
    (kept : rawInactiveRetained gates selected wire shift reference history hidden) :
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).toOuterMeasure
      {oracle | RawGarblingMatches (rawGatesWithLabels gates
        (rawMixedLabels selected publicLabel wire shift hidden)) oracle ∧
          PermutationTranscriptMatches oracle history} =
      ∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history (rawActiveDomains gates selected publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial := by
  classical
  let labels := rawMixedLabels selected publicLabel wire shift hidden
  let covered := rawActiveDomains gates selected publicLabel
  have retained : ∀ index, labels (rawLabelBucket index) (rawSlotBranch index.slot) ∉
      forbiddenSlotLabels (rawBucketTweak gates index) (rawBucketOffset gates index)
        (fun query : ResidualFixedQueryDomain history covered index => query.1.1)
        (fun query : ResidualFixedQueryDomain history covered index => reference.permutation index query.1.1) := by
    intro index
    by_cases active : rawSlotBranch index.slot = selected (rawLabelBucket index)
    · have domains : ∀ use : RawBucketUse gates index,
          ∀ query : ResidualFixedQueryDomain history covered index,
          publicLabel (rawLabelBucket index) ^^^ rawBucketTweak gates index use ≠ query.1.1 := by
        intro use query equal
        apply query.2
        change query.1.1 ∈ rawActiveDomains gates selected publicLabel index
        rw [rawActiveDomains, if_pos active]
        exact ⟨use, equal⟩
      apply not_mem_forbidden_of_disjoint
      · intro use query
        simpa only [labels, rawMixedLabels, if_pos active] using domains use query
      · intro use query equal
        apply domains use query
        apply (reference.permutation index).injective
        rw [referenceActive index active use]
        simpa only [labels, rawMixedLabels, if_pos active] using equal
    · have earlier := kept ⟨index, active⟩
      apply not_mem_forbidden_of_disjoint
      · intro use query
        simpa only [labels, rawMixedLabels, if_neg active] using
          slotInput_ne_queryDomain (rawBucketTweak gates index) (rawBucketOffset gates index)
            (fun query : FixedQueryDomain history index => query.1)
            (fun query : FixedQueryDomain history index => reference.permutation index query.1)
            (hidden (wire (rawLabelBucket index)) ^^^ shift (rawLabelBucket index)) earlier use query.1
      · intro use query
        simpa only [labels, rawMixedLabels, if_neg active] using
          slotOutput_ne_queryRange (rawBucketTweak gates index) (rawBucketOffset gates index)
            (fun query : FixedQueryDomain history index => query.1)
            (fun query : FixedQueryDomain history index => reference.permutation index query.1)
            (hidden (wire (rawLabelBucket index)) ^^^ shift (rawLabelBucket index)) earlier use query.1
  apply rawCoveredFixedTranscript_mass (rawGatesWithLabels gates labels) reference history covered compatible
  · intro index domain member
    change domain ∈ rawActiveDomains gates selected publicLabel index at member
    by_cases active : rawSlotBranch index.slot = selected (rawLabelBucket index)
    · rw [rawActiveDomains, if_pos active] at member
      obtain ⟨use, same⟩ := member
      dsimp only at same
      refine ⟨use, ?_, ?_⟩
      · rw [rawGatesWithLabels_domain]
        simpa only [labels, rawMixedLabels, if_pos active] using same
      · rw [rawGatesWithLabels_range]
        have assigned := referenceActive index active use
        rw [same] at assigned
        simpa only [labels, rawMixedLabels, if_pos active] using assigned.symm
    · simp [rawActiveDomains, active] at member
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
theorem rawSharedInactive_residual_mass_ge :
    (1 - ∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain history index.1) : Nat) : ℝ≥0∞) / Fintype.card Block) *
      (∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain history (rawActiveDomains gates selected publicLabel) index))).factorial :
          ℝ≥0∞) / (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels gates
          (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
            PermutationTranscriptMatches sample.1 history} := by
  classical
  apply (mul_le_mul_left
    (rawInactiveRetained_mass_ge gates selected wire shift reference history) _).trans
  rw [uniform_prod_eq_bind, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro hidden
  by_cases kept : rawInactiveRetained gates selected wire shift reference history hidden
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, kept, if_true,
      PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
    rw [rawMixedCoveredTranscript_mass gates selected wire shift reference history publicLabel compatible
      tweaksDistinct offsetsDistinct referenceActive hidden kept]
  · simp [Set.indicator_apply, kept]

end ResidualLabels

/-- This bound combines the actual raw garbler view and the actual real handler transcript. -/
theorem rawSharedInactive_realTranscript_mass_ge {Gate Wire : Type}
    [Fintype Gate] [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (gates : Gate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (publicLabel : RawLabelBucket → Block) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (tweaksDistinct : ∀ index, Function.Injective (rawBucketTweak gates index))
    (offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
    (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
      ∀ use : RawBucketUse gates index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) ^^^ rawBucketTweak gates index use) =
            rawBucketOffset gates index use ^^^ publicLabel (rawLabelBucket index)) :
    (1 - ∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse gates index.1) *
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) : Nat) : ℝ≥0∞) /
          Fintype.card Block) *
      (∏ index, ((Fintype.card Block - (Fintype.card (RawBucketUse gates index) +
        Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
          (rawActiveDomains gates selected publicLabel) index))).factorial : ℝ≥0∞) /
            (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches (rawGatesWithLabels gates
          (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} transcript} := by
  have fixed := (realOracleTranscriptCompatible_iff randomness transcript).mp compatible
  have event : {sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block) |
      RawGarblingMatches (rawGatesWithLabels gates
        (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} =
      {sample | RawGarblingMatches (rawGatesWithLabels gates
        (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
        PermutationTranscriptMatches sample.1 (fixedOracleTranscriptRecords transcript)} := by
    ext sample
    simp only [Set.mem_setOf_eq, realOracleTranscriptCompatible_iff,
      nonFixedTranscriptCompatible_update, fixed.2, and_true]
  rw [event]
  exact rawSharedInactive_residual_mass_ge gates selected wire shift randomness.fixedKeyOracle
    (fixedOracleTranscriptRecords transcript) publicLabel fixed.1 tweaksDistinct offsetsDistinct referenceActive

end
end Kriterion.ArgoMAC.Security
