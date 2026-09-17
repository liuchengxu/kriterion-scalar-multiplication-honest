import Proof.Privacy.Source.GoodLinkedCurveRatio
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype instFintypeEncQueryDomainOfBlock
  bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1
  rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

set_option maxRecDepth 4096 in
/-- A complete good source needs only the nonfixed reference replies. -/
theorem fullSourceGood_curve_nonfixed_mass_ge
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
        if NonFixedTranscriptCompatible
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
  by_cases compatible : NonFixedTranscriptCompatible
    {randomness with hashOracle := hash} (before ++ after)
  · have changed : OracleTranscriptCompatible Garbling.oracleHandler
        {{randomness with fixedKeyOracle := reference.1} with hashOracle := hash} (before ++ after) := by
      rw [realOracleTranscriptCompatible_iff]
      refine ⟨fixed, ?_⟩
      change NonFixedTranscriptCompatible
        {{randomness with hashOracle := hash} with fixedKeyOracle := reference.1} _
      exact (nonFixedTranscriptCompatible_update _ _ _).mpr compatible
    simp only [if_pos compatible, if_pos changed, le_refl]
  · simp only [if_neg compatible, zero_le]

end
end Kriterion.ArgoMAC.Security
