import Proof.Privacy.Source.IndependentCurveSourceRatio
import Proof.Privacy.Source.LinkedTagKeyMass
import Proof.Privacy.Source.LinkedGuardedAverage
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual linked source dominates the guarded curve schedule density. -/
theorem actualLinkedCurveSource_mass_ge
    [Fintype Block] [Fintype BaseField] [Fintype Pipeline.FixedKeyIndex]
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (source : CircuitMaskSample)
    (keys : RawCircuitGate → BitAdaptor.Key) (lifts : RawCircuitGate → FullHashLift)
    (randomizers : CircuitSourceRandomizers source pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField source gate = ((lifts gate).val : BaseField))
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : AffineInput) (curveMac : InputMac)
    (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (miss : bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (lengthBound : (before ++ after).length ≤ budget)
    (encFits : ∀ index, 2 + Fintype.card (EncQueryDomain (encOracleTranscriptRecords (before ++ after)) index) ≤
      Fintype.card Block)
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
    ((1 - ((4 * budget : Nat) : ℝ≥0∞) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords (before ++ after))) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with hashOracle := hash} (before ++ after) then
          (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      ((1 - ((182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞) +
      508 / (Fintype.card Block : ℝ≥0∞))) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} (curve.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) else 0) ≤
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        source lifts (inputSelectedLabelBit input) (inputMacCoordinateEquiv curveMac) (before ++ after)) := by
  have linked := actualLinkedTagKey_guarded_mass_ge outputKeys pointRandomness bridgeKey r1 r2 mask
    randomness source lifts (inputSelectedLabelBit input) (inputMacCoordinateEquiv curveMac)
    (before ++ after) miss budget lengthBound encFits
  apply le_trans _ linked
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro hash
  apply mul_le_mul_right
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with hashOracle := hash} (before ++ after)
  · rw [if_pos compatible]
    exact actualIndependentCurveSource_mass_ge outputKeys pointRandomness bridgeKey r1 r2 mask.value
      source keys lifts randomizers residues curve points input curveMac
      {randomness with hashOracle := hash} before after compatible offsetsDistinct referenceActive
      state historyMembers fresh reference priorFits residualFits
  · simp only [if_neg compatible, zero_le]

end
end Kriterion.ArgoMAC.Security
