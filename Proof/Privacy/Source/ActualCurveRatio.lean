import Proof.Privacy.Collision.CurveScheduleDomains
import Proof.Privacy.Source.ActualAdaptiveRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- The actual invalid schedule supplies the exposed and residual domain counts. -/
theorem actualCurveProgrammedSource_mass_ratio
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac pointMac : InputMac)
    (wire : RawLabelBucket → Bool → Wire) (shift : RawLabelBucket → Bool → Block)
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
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} (curve.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (partialRawLabels (curveOnlyExposed (circuitBucketInputBit input)) (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} (before ++ after)} := by
  apply partialCircuitProgrammedSource_mass_ratio keys slopes lifts tables
    (curveOnlyExposed (circuitBucketInputBit input)) wire shift
    (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket)
    randomness (before ++ after) compatible offsetsDistinct referenceActive
    state (curve.schedule input curveMac) (fixedOracleTranscriptRecords after) fresh reference
    (fun index => curveGateProgramRecords_exposedCount curve points input curveMac pointMac
      keys slopes lifts tables index) _ priorFits residualFits
  intro index
  have domains : programmedDomains (gateProgramRecords (curve.schedule input curveMac)) =
      partialActiveDomains (circuitRawGatePrescription keys slopes lifts tables)
        (curveOnlyExposed (circuitBucketInputBit input))
        (fun bucket _ => circuitBucketInputLabel curveMac pointMac bucket) := by
    funext index
    exact curveGateProgramRecords_domains curve points input curveMac pointMac
      keys slopes lifts tables index
  rw [domains]
  apply residualFixedQueryDomain_card_congr
  intro record
  rw [fixedOracleTranscriptRecords_append before after]; simp only [List.mem_append, historyMembers]

/-- The actual curve records supply the exposed raw equations. -/
theorem curveGateProgramRecords_referenceActive
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (compatible : PermutationTranscriptMatches oracle (gateProgramRecords
      (curve.schedule input curveInputMac))) :
    ∀ index, curveOnlyExposed (circuitBucketInputBit input) (rawLabelBucket index)
        (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys slopes lifts tables) index,
        oracle.permutation index
          (circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) ^^^
            rawBucketTweak (circuitRawGatePrescription keys slopes lifts tables) index use) =
          rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index use ^^^
            circuitBucketInputLabel curveInputMac pointInputMac (rawLabelBucket index) := by
  intro index active use
  have exposed : isCurveIndex index ∧
      rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) := by
    rcases index with ⟨kind, position, slot⟩
    cases kind with
    | curve adaptor => exact ⟨True.intro, of_decide_eq_true active⟩
    | point coordinate adaptor => cases active
  rcases exposed with ⟨curveIndex, activeBit⟩
  rcases use with ⟨⟨gate, slot⟩, sameIndex⟩
  subst index
  have selected : rawSlotBranch slot =
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit := by
    rw [actualCircuitDirective_bit curve points input curveInputMac pointInputMac gate slot]
    exact activeBit
  have rawLaw := recordLaw gate slot selected
  have labelLaw : (circuitRawGatePrescription keys slopes lifts tables gate).label slot =
      circuitBucketInputLabel curveInputMac pointInputMac
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) := by
    have domains := congrArg PermutationRecord.domain rawLaw
    change (actualCircuitDirective curve points input curveInputMac pointInputMac gate).label ^^^
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).location.tweak =
      (circuitRawGatePrescription keys slopes lifts tables gate).label slot ^^^
        (rawCircuitLocation gate).tweak at domains
    rw [actualCircuitDirective_location, actualCircuitDirective_label curve points input
      curveInputMac pointInputMac gate slot] at domains
    have cancelled := congrArg (fun value => value ^^^ (rawCircuitLocation gate).tweak) domains
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using cancelled.symm
  have member : (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot ∈
      gateProgramRecords (curve.schedule input curveInputMac) := by
    apply (curveGateProgramRecords_filter curve points input curveInputMac pointInputMac _).mpr
    refine ⟨?_, ?_⟩
    · exact (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac _).mpr
        ⟨gate, slot, selected, rfl⟩
    · rw [actualCircuitDirective_slotRecord_index]
      exact curveIndex
  have matched := compatible _ member
  rw [rawLaw] at matched
  change oracle.permutation _
    ((circuitRawGatePrescription keys slopes lifts tables gate).label slot ^^^
      (rawCircuitLocation gate).tweak) =
    (circuitRawGatePrescription keys slopes lifts tables gate).offset slot ^^^
      (circuitRawGatePrescription keys slopes lifts tables gate).label slot at matched
  rw [labelLaw] at matched
  exact matched


end
end Kriterion.ArgoMAC.Security
