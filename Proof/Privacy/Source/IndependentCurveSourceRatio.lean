import Proof.Privacy.Source.PadRestrictedKeyMass
import Proof.Privacy.Source.PadRestrictedCurveRatio
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The selected coordinate labels give every public curve label. -/
theorem inputMacCoordinate_bucket (mac : InputMac) (bucket : RawLabelBucket) :
    inputMacCoordinateEquiv mac (circuitBucketWire bucket) =
      circuitBucketInputLabel mac mac bucket := by
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor => cases adaptor <;> rfl
  | point coordinate adaptor => cases coordinate <;> cases adaptor <;> rfl

set_option maxHeartbeats 2000000 in
/-- The actual independent source keeps its tag, transcript, and pad guard. -/
theorem actualIndependentCurveSource_mass_ge
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 mask : BaseField) (source : CircuitMaskSample)
    (keys : RawCircuitGate → BitAdaptor.Key) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac : InputMac)
    (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after))
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys (circuitSourceSlope source) lifts (circuitSourceTable source)) index))
    (referenceActive : ∀ index, (curveOnlyExposed (circuitBucketInputBit input)) (rawLabelBucket index) (rawSlotBranch index.slot) = true →
      ∀ use : RawBucketUse (circuitRawGatePrescription keys (circuitSourceSlope source) lifts (circuitSourceTable source)) index,
        randomness.fixedKeyOracle.permutation index
          ((fun bucket _ => circuitBucketInputLabel curveMac curveMac bucket) (rawLabelBucket index) (rawSlotBranch index.slot) ^^^
            rawBucketTweak (circuitRawGatePrescription keys (circuitSourceSlope source) lifts (circuitSourceTable source)) index use) =
          rawBucketOffset (circuitRawGatePrescription keys (circuitSourceSlope source) lifts (circuitSourceTable source)) index use ^^^
            (fun bucket _ => circuitBucketInputLabel curveMac curveMac bucket) (rawLabelBucket index) (rawSlotBranch index.slot))
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
        (partialActiveDomains (circuitRawGatePrescription keys (circuitSourceSlope source) lifts (circuitSourceTable source)) (curveOnlyExposed (circuitBucketInputBit input)) (fun bucket _ => circuitBucketInputLabel curveMac curveMac bucket))
          index) ≤ Fintype.card Block) :
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      ((1 - ((182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞) +
      508 / (Fintype.card Block : ℝ≥0∞))) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} (curve.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) ≤
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × (InputMacKey × InputMacKey))).toOuterMeasure
      {sample | (independentKeyLabelsEquiv (inputSelectedLabelBit input) sample.2).1 = inputMacCoordinateEquiv curveMac ∧
        independentFullCircuitSource outputKeys pointRandomness bridgeKey mask r1 r2
          sample.2.2 sample.2.1 (circuitSourceQuotients source) sample.1 = (lifts, sourceCiphertexts source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} (before ++ after) ∧
        EncSourceGood sample.2.1 sample.2.2} := by
  rw [actualIndependentSource_guardedKeyMass outputKeys pointRandomness bridgeKey r1 r2 mask
    randomness source lifts keys randomizers residues (inputSelectedLabelBit input)
    (inputMacCoordinateEquiv curveMac) (before ++ after)]
  apply mul_le_mul_right
  have bound := actualCurveProgrammedSource_guard_mass_ratio keys (circuitSourceSlope source)
    lifts (circuitSourceTable source) curve points input curveMac curveMac
    independentBucketWire (fun _ _ => 0) (inputSelectedLabelBit input)
    (inputMacCoordinateEquiv curveMac) randomness before after compatible offsetsDistinct
    referenceActive state historyMembers fresh reference priorFits residualFits
  apply bound.trans_eq
  apply congrArg (fun event : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) ×
    (IndependentLabelWire → Block)) => (PMF.uniformOfFintype _).toOuterMeasure event)
  ext sample
  have bits : circuitBucketInputBit input = fun bucket =>
      inputSelectedLabelBit input (circuitBucketWire bucket) := funext (circuitBucketInputBit_wire input)
  simp only [Set.mem_setOf_eq, bits, inputMacCoordinate_bucket]

end
end Kriterion.ArgoMAC.Security
