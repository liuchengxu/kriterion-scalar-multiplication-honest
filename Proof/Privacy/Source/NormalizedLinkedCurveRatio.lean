import Proof.Privacy.Source.LinkedCurveSourceRatio
import Proof.Privacy.Source.FullCircuitSourceDensity
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This density normalizes the full tag in the real source sum. -/
def fullSourceTagDensity [Fintype Block] (tag : FullCircuitSource) : ℝ≥0∞ :=
  (PMF.uniformOfFintype FullCircuitSource) tag

private theorem fullSourceTagDensity_product [Fintype Block]
    [fixedFinite : Fintype Pipeline.FixedKeyIndex] (tag : FullCircuitSource) :
    fullSourceTagDensity tag = ∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹ := by
  have same : fixedFinite = Pipeline.instFintypeFixedKeyIndex := Subsingleton.elim _ _
  have products := congrArg (fun finite : Fintype Pipeline.FixedKeyIndex =>
    letI := finite
    ∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) same
  exact (fullCircuitSource_uniform_mass tag).trans products.symm

set_option maxRecDepth 2048 in
/-- The inverse tag density converts the linked tag count to the normalized source weight. -/
theorem actualLinkedCurveSource_normalized_mass_ge
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
      (fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} (curve.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) else 0) ≤
    (fullSourceTagDensity (lifts, sourceCiphertexts source))⁻¹ *
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask randomness
        source lifts (inputSelectedLabelBit input) (inputMacCoordinateEquiv curveMac) (before ++ after)) := by
  set density := fullSourceTagDensity (lifts, sourceCiphertexts source)
  have nonzero : density ≠ 0 := by
    simp only [density, fullSourceTagDensity, PMF.uniformOfFintype_apply, ne_eq, ENNReal.inv_eq_zero]
    exact ENNReal.natCast_ne_top _
  have finite : density ≠ ⊤ := by
    simp only [density, fullSourceTagDensity, PMF.uniformOfFintype_apply, ne_eq, ENNReal.inv_eq_top]
    exact_mod_cast Fintype.card_ne_zero (α := FullCircuitSource)
  have cancel : density⁻¹ * density = 1 := ENNReal.inv_mul_cancel nonzero finite
  have bound := actualLinkedCurveSource_mass_ge outputKeys pointRandomness bridgeKey r1 r2 mask source
    keys lifts randomizers residues curve points input curveMac randomness before after miss budget lengthBound
    encFits offsetsDistinct referenceActive state historyMembers fresh reference priorFits residualFits
  have scaled := mul_le_mul_right bound density⁻¹
  apply le_trans _ scaled
  apply le_of_eq
  simp only [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro hash
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with hashOracle := hash} (before ++ after)
  · simp only [if_pos compatible]
    rw [← fullSourceTagDensity_product (lifts, sourceCiphertexts source)]
    have densityEq : fullSourceTagDensity (lifts, sourceCiphertexts source) = density := rfl
    rw [densityEq]
    calc
      _ = (density⁻¹ * density) * _ := by rw [cancel, one_mul]
      _ = _ := by
        have reorder (d a h c b f m : ENNReal) :
            (d⁻¹ * d) * (a * (h * (c * (b * (f * m))))) =
              d⁻¹ * (a * (h * (c * (b * (d * f * m))))) := by ac_rfl
        exact reorder _ _ _ _ _ _ _
  · simp only [if_neg compatible, mul_zero]

end
end Kriterion.ArgoMAC.Security
