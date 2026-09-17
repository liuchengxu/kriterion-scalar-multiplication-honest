import Proof.Privacy.Source.ActualCurveRatio
import Proof.Privacy.Collision.PadRestrictedCount
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- The actual curve schedule keeps the pad restriction in its relative source count. -/
theorem actualCurveProgrammedSource_guard_mass_ratio
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (wire : RawLabelBucket → Bool → IndependentLabelWire) (shift : RawLabelBucket → Bool → Block)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after))
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (referenceActive : ∀ index, (curveOnlyExposed (circuitBucketInputBit input)) (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        randomness.fixedKeyOracle.permutation index
          ((fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) (rawLabelBucket index) (rawSlotBranch index.slot) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) (rawLabelBucket index) (rawSlotBranch index.slot))
    (state : SimulatorState)
    (historyMembers : ∀ record, record ∈ state.fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords before)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords (curve.schedule input curveMac)))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords (curve.schedule input curveMac)) ++ (fixedOracleTranscriptRecords after)))
    (priorFits : ∀ index, circuitBucketSize index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index +
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords (before ++ after))
        (partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables) (curveOnlyExposed (circuitBucketInputBit input)) (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket))
          index) ≤ Fintype.card Block) :
    (1 - ((182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞) +
      508 / (Fintype.card Block : ℝ≥0∞))) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} (curve.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (IndependentLabelWire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (partialRawLabels (curveOnlyExposed (circuitBucketInputBit input)) (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} (before ++ after) ∧
          EncSourceGood ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).1
            ((independentKeyLabelsEquiv selected).symm (publicLabels, sample.2)).2} := by
  let exposed := curveOnlyExposed (circuitBucketInputBit input)
  let publicLabel := fun bucket (_ : Bool) => circuitBucketInputLabel curveMac pointMac bucket
  let gates := circuitRawGatePrescription keys slopes lifts tables
  have counts := fun index => curveGateProgramRecords_exposedCount curve points input curveMac pointMac
    keys slopes lifts tables index
  rw [programGateSchedule_sourceMass_product state (curve.schedule input curveMac)
    (fixedOracleTranscriptRecords after) fresh reference circuitBucketSize
    (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot)) counts]
  have domains : programmedDomains (gateProgramRecords (curve.schedule input curveMac)) =
      partialActiveDomains gates exposed publicLabel := by
    funext index
    exact curveGateProgramRecords_domains curve points input curveMac pointMac keys slopes lifts tables index
  have residualCounts (index : Pipeline.FixedKeyIndex) :
      Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ fixedOracleTranscriptRecords after)
        (programmedDomains (gateProgramRecords (curve.schedule input curveMac))) index) =
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords (before ++ after))
        (partialActiveDomains gates exposed publicLabel) index) := by
    rw [domains]
    apply residualFixedQueryDomain_card_congr
    intro record
    rw [fixedOracleTranscriptRecords_append before after]; simp only [List.mem_append, historyMembers]
  simp_rw [residualCounts]
  have fixed := (realOracleTranscriptCompatible_iff randomness (before ++ after)).mp compatible
  have bound := independentCircuit_guard_mass_ge keys slopes lifts tables exposed wire shift
    randomness.fixedKeyOracle (before ++ after) publicLabel selected publicLabels fixed.1
    offsetsDistinct referenceActive
  have factor := adaptiveIdealPermutationFactor_le (Fintype.card Block) circuitBucketSize
    (fun index => Fintype.card (FixedQueryDomain state.fixedTranscript index))
    (fun index => Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords (before ++ after))
      (partialActiveDomains gates exposed publicLabel) index))
    (fun index => exposed (rawLabelBucket index) (rawSlotBranch index.slot)) Fintype.card_pos
    priorFits residualFits
  apply (mul_le_mul_right factor _).trans
  convert bound using 1
  all_goals try rfl
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq, realOracleTranscriptCompatible_iff,
    nonFixedTranscriptCompatible_update, fixed.2, and_true]
  rfl

end
end Kriterion.ArgoMAC.Security
