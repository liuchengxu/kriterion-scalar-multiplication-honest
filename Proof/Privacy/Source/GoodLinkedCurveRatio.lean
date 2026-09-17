import Proof.Privacy.Source.NormalizedLinkedCurveRatio
import Proof.Privacy.Source.FullSourceGood
import Proof.Privacy.Source.SourceCapacity
import Proof.Privacy.Source.ActualSourceRatio
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual linked event ignores the reference fixed oracle. -/
theorem actualLinkedTagKeyEvent_fixedOracle
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey r1 r2 : BaseField) (mask : NonZeroBase) (randomness : Garbling.Randomness)
    (source : CircuitMaskSample) (lifts : RawCircuitGate → FullHashLift)
    (selected : EncPRF.PermutationIndex → Bool) (publicLabels : EncPRF.PermutationIndex → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) :
    actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask
      {randomness with fixedKeyOracle := oracle} source lifts selected publicLabels transcript =
    actualLinkedTagKeyEvent outputKeys pointRandomness bridgeKey r1 r2 mask
      randomness source lifts selected publicLabels transcript := rfl

/-- The extension oracle answers the full external fixed transcript. -/
theorem curveExtension_matches (state : SimulatorState) (schedule : List GateDirective)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ fixedOracleTranscriptRecords after)) :
    PermutationTranscriptMatches reference.1 (fixedOracleTranscriptRecords (before ++ after)) := by
  intro record member
  rw [fixedOracleTranscriptRecords_append, List.mem_append] at member
  apply reference.2 record
  rcases member with prior | later
  · exact List.mem_append_left _ ((mem_programRecordHistory_iff _ _ _).mpr
      (Or.inr ((members record).mpr prior)))
  · exact List.mem_append_right _ later

private theorem curveExposed_labels (curveMac pointMac : InputMac)
    (input : AffineInput) (index : Pipeline.FixedKeyIndex)
    (active : curveOnlyExposed (circuitBucketInputBit input) (rawLabelBucket index)
      (rawSlotBranch index.slot) = true) :
    circuitBucketInputLabel curveMac pointMac (rawLabelBucket index) =
      circuitBucketInputLabel curveMac curveMac (rawLabelBucket index) := by
  rcases index with ⟨kind, position, slot⟩
  cases kind with
  | curve adaptor => cases adaptor <;> rfl
  | point coordinate adaptor => cases active

set_option maxRecDepth 2048 in
/-- The complete good source supplies the curve reference equations. -/
theorem fullSourceGood_curve_reference
    (coin : SimulatorCoin) (mask : BaseField) (rows : FieldMacToECMac.Rows)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (input : AffineInput) (complete : FullSourceComplete full.1)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (matching : PermutationTranscriptMatches oracle (gateProgramRecords
      ((circuitMaskSampleGarble coin.bridgeKey mask rows input (decodeFullSource full)).curveRequest.schedule
        input (coin.inputKey.encodeAffine input)))) :
    let pointKey := EncPRF.transformKey coin.oracles.encOracle
      (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
    let gates := sourceGatePrescription (decodeFullSource full) pointKey coin.inputKey full.1
    ∀ index, curveOnlyExposed (circuitBucketInputBit input) (rawLabelBucket index)
      (rawSlotBranch index.slot) = true → ∀ use : RawBucketUse gates index,
      oracle.permutation index
        (circuitBucketInputLabel (coin.inputKey.encodeAffine input) (coin.inputKey.encodeAffine input)
          (rawLabelBucket index) ^^^ rawBucketTweak gates index use) =
      rawBucketOffset gates index use ^^^
        circuitBucketInputLabel (coin.inputKey.encodeAffine input) (coin.inputKey.encodeAffine input)
          (rawLabelBucket index) := by
  rw [← decodeFullSource_lifts full complete]
  dsimp only
  let source := decodeFullSource full
  let pointKey := EncPRF.transformKey coin.oracles.encOracle
    (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
  let sample := circuitMaskSampleGarble coin.bridgeKey mask rows input source
  have law := curveGateProgramRecords_referenceActive sample.curveRequest sample.pointRequests input
    (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input) (circuitGateKey pointKey coin.inputKey)
    (circuitSourceSlope source) (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    (circuitSourceTable source)
    (fun gate slot active => circuitMaskDirective_record_eq_raw coin.bridgeKey mask rows input source
      coin.inputKey pointKey gate slot active) oracle matching
  intro index active use
  have bound := law index active use
  have labels := curveExposed_labels (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input)
    input index active
  rw [labels] at bound
  exact bound



set_option maxRecDepth 4096 in
/-- A complete good source supplies the actual normalized curve lower bound. -/
theorem fullSourceGood_curve_mass_ge
    [Fintype Block] [Fintype BaseField]
    (coin : SimulatorCoin) (mask : NonZeroBase) (rows : FieldMacToECMac.Rows)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (input : AffineInput) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (randomness : Garbling.Randomness)
    (outputKeys : FieldMacToECMac.OutputKeys) (pointRandomness : FieldMacToECMac.Randomness)
    (r1 r2 : BaseField)
    (randomizers : CircuitSourceRandomizers (decodeFullSource full) pointRandomness r1 r2)
    (residues : ∀ gate, circuitSourceField (decodeFullSource full) gate = ((full.1 gate).val : BaseField))
    (complete : FullSourceComplete full.1)
    (good : ¬ rawSourceBad coin (decodeFullSource full) input before)
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (miss : coin.bridgeKey ∉ transcriptHashInputs (before ++ after))
    (budget : Nat) (small : budget < 2 ^ 100) (lengthBound : (before ++ after).length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := decodeFullSource full
    let sample := circuitMaskSampleGarble coin.bridgeKey mask.value rows input source
    let curveMac := coin.inputKey.encodeAffine input
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
          programGateSchedule {state with fixedOracle := oracle.1} (sample.curveRequest.schedule input curveMac))).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) else 0) ≤
    (fullSourceTagDensity (full.1, sourceCiphertexts source))⁻¹ *
    (PMF.uniformOfFintype (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))).toOuterMeasure
      (actualLinkedTagKeyEvent outputKeys pointRandomness coin.bridgeKey r1 r2 mask randomness
        source full.1 (inputSelectedLabelBit input) (inputMacCoordinateEquiv curveMac) (before ++ after)) := by
  intro source sample curveMac
  let pointKey := EncPRF.transformKey coin.oracles.encOracle
    (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
  let keys := circuitGateKey pointKey coin.inputKey
  let mass := ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
    programGateSchedule {state with fixedOracle := oracle.1} (sample.curveRequest.schedule input curveMac))).toOuterMeasure
      {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)}
  have fresh := rawSourceGood_curve coin state mask.value rows source input before members good
  by_cases zero : mass = 0
  · dsimp only [mass] at zero
    simp only [zero, mul_zero, ite_self, tsum_zero, zero_le]

  let reference := Classical.choice (programGateSchedule_extension_of_mass_ne_zero state
    (sample.curveRequest.schedule input curveMac) (fixedOracleTranscriptRecords after) fresh zero)
  have fixed := curveExtension_matches state (sample.curveRequest.schedule input curveMac) before after members reference
  have active := fullSourceGood_curve_reference coin mask.value rows full input complete reference.1 (by
    intro record member
    exact reference.2 record (List.mem_append_left _
      ((mem_programRecordHistory_iff _ _ _).mpr (Or.inl member))))
  have beforeLength : before.length ≤ budget := by
    have : (before ++ after).length = before.length + after.length := List.length_append
    omega
  have bound := actualLinkedCurveSource_normalized_mass_ge outputKeys pointRandomness coin.bridgeKey r1 r2
    mask source keys full.1 randomizers residues sample.curveRequest sample.pointRequests input curveMac
    {randomness with fixedKeyOracle := reference.1} before after miss budget lengthBound
    (sourceEncCapacity _ budget small lengthBound)
    (fullSourceGood_offsets coin full input before complete good) active state members fresh reference
    (sourcePriorCapacity state before members budget small beforeLength)
    (sourceResidualCapacity _ _ budget small lengthBound)
  have eventEq := actualLinkedTagKeyEvent_fixedOracle outputKeys pointRandomness coin.bridgeKey r1 r2
    mask randomness source full.1 (inputSelectedLabelBit input) (inputMacCoordinateEquiv curveMac)
    (before ++ after) reference.1
  have rightEq := congrArg (fun event : Set (((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey) ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) =>
    (fullSourceTagDensity (full.1, sourceCiphertexts source))⁻¹ *
      (PMF.uniformOfFintype _).toOuterMeasure event) eventEq
  have bound := bound.trans_eq rightEq
  apply le_trans _ bound
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro hash
  apply mul_le_mul_right
  by_cases compatible : OracleTranscriptCompatible Garbling.oracleHandler
    {randomness with hashOracle := hash} (before ++ after)
  · have changed : OracleTranscriptCompatible Garbling.oracleHandler
        {{randomness with fixedKeyOracle := reference.1} with hashOracle := hash} (before ++ after) := by
      rw [realOracleTranscriptCompatible_iff] at compatible ⊢
      refine ⟨fixed, ?_⟩
      change NonFixedTranscriptCompatible
        {{randomness with hashOracle := hash} with fixedKeyOracle := reference.1} _
      exact (nonFixedTranscriptCompatible_update _ _ _).mpr compatible.2
    simp only [if_pos compatible, if_pos changed, le_refl]
  · simp only [if_neg compatible, zero_le]

end
end Kriterion.ArgoMAC.Security
