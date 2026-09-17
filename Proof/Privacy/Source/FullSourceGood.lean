import Proof.Privacy.Collision.ConcreteRetainedBadBound
import Proof.Privacy.Source.ActualAdaptiveRatio
import Proof.Privacy.Source.RealSourceSum
import Proof.Privacy.Collision.CurveScheduleDomains

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- A good source keeps every raw bucket injective. -/
theorem rawSourceGood_offsets (coin : SimulatorCoin) (source : CircuitMaskSample)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (good : ¬ rawSourceBad coin source input history) :
    ∀ index, Function.Injective (rawBucketOffset
      (sourceGatePrescription source
        (EncPRF.transformKey coin.oracles.encOracle
          (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey)
        coin.inputKey (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index) := by
  classical
  exact not_not.mp (not_or.mp good).1

/-- A good source keeps each exposed selected record fresh. -/
theorem rawSourceGood_fresh (coin : SimulatorCoin) (source : CircuitMaskSample)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (good : ¬ rawSourceBad coin source input history) :
    ∀ gate slot,
      rawSlotBranch slot = circuitBucketInputBit input
        (rawLabelBucket (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) →
      (OnCurve input ∨ ∃ adaptor bit, gate = .inl (adaptor, bit)) →
      let record := (sourceGatePrescription source
        (EncPRF.transformKey coin.oracles.encOracle
          (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey)
        coin.inputKey (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) gate).slotRecord slot
      FreshPermutationPair (fixedOracleTranscriptRecords history) record.index record.domain record.range := by
  classical
  exact not_not.mp (not_or.mp good).2

/-- Complete decoding keeps the original full lift tape. -/
theorem fullSourceGood_offsets (coin : SimulatorCoin)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (complete : FullSourceComplete full.1)
    (good : ¬ rawSourceBad coin (decodeFullSource full) input history) :
    ∀ index, Function.Injective (rawBucketOffset
      (sourceGatePrescription (decodeFullSource full)
        (EncPRF.transformKey coin.oracles.encOracle
          (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey)
        coin.inputKey full.1) index) := by
  rw [← decodeFullSource_lifts full complete]
  exact rawSourceGood_offsets coin (decodeFullSource full) input history good

/-- The actual prefix records exactly its supported fixed queries. -/
theorem sourcePrefix_history {Result : Type} {budget : Nat} (coin : SimulatorCoin)
    (program : OracleProgram Garbling.oracleSpec Result budget)
    (selected : Result × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))
    (member : selected ∈ (runOracleProgramWithTranscript idealOracleHandler program coin.state.oracle).support)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ selected.2.1.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords selected.2.2 := by
  rw [runTranscript_finalState idealOracleHandler program coin.state.oracle selected member]
  exact idealTranscriptFinal_fixedHistory_members coin.state.oracle selected.2.2
    (runOracleProgramWithTranscript_compatible idealOracleHandler program coin.state.oracle selected member) rfl record

/-- A good valid source gives the actual pipeline a fresh schedule. -/
theorem rawSourceGood_pipeline (coin : SimulatorCoin) (state : SimulatorState)
    (mask : BaseField) (rows : FieldMacToECMac.Rows) (source : CircuitMaskSample)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords history)
    (valid : OnCurve input) (good : ¬ rawSourceBad coin source input history) :
    let sample := circuitMaskSampleGarble coin.bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input)
        ((EncPRF.transformKey coin.oracles.encOracle
          (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey).encodeAffine input))) := by
  apply circuitMaskSchedule_fresh
  · exact rawSourceGood_offsets coin source input history good
  · intro gate slot active
    dsimp only
    intro prior member same
    exact rawSourceGood_fresh coin source input history good gate slot active (Or.inl valid)
      prior ((members prior).mp member) same


/-- A good source gives the curve layer a fresh schedule on either branch. -/
theorem rawSourceGood_curve (coin : SimulatorCoin) (state : SimulatorState)
    (mask : BaseField) (rows : FieldMacToECMac.Rows) (source : CircuitMaskSample)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords history)
    (good : ¬ rawSourceBad coin source input history) :
    let sample := circuitMaskSampleGarble coin.bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript
      (gateProgramRecords (sample.curveRequest.schedule input (coin.inputKey.encodeAffine input))) := by
  dsimp only
  let pointKey := EncPRF.transformKey coin.oracles.encOracle
    (EncPRF.whiteningKeys coin.oracles.hashOracle coin.bridgeKey) coin.inputKey
  let sample := circuitMaskSampleGarble coin.bridgeKey mask rows input source
  apply freshRecordSchedule_of_pairwise
  · intro record member
    rcases (mem_curveGateProgramRecords_iff sample.curveRequest input
      (coin.inputKey.encodeAffine input) record).mp member with ⟨adaptor, bit, slot, active, rfl⟩
    have law := circuitMaskDirective_record_eq_raw coin.bridgeKey mask rows input source
      coin.inputKey pointKey (.inl (adaptor, bit)) slot active
    change FreshPermutationPair state.fixedTranscript
      ((actualCircuitDirective sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input) (.inl (adaptor, bit))).slotRecord slot).index
      ((actualCircuitDirective sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input) (.inl (adaptor, bit))).slotRecord slot).domain
      ((actualCircuitDirective sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input) (.inl (adaptor, bit))).slotRecord slot).range
    rw [law]
    intro prior member same
    apply rawSourceGood_fresh coin source input history good (.inl (adaptor, bit)) slot
      (active.trans (actualCircuitDirective_bit sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input) (.inl (adaptor, bit)) slot)) (Or.inr ⟨adaptor, bit, rfl⟩)
      prior ((members prior).mp member) same
  · have pairwise := pipelineGateProgramRecords_pairwise sample.curveRequest sample.pointRequests input
      (coin.inputKey.encodeAffine input) (pointKey.encodeAffine input)
      (circuitGateKey pointKey coin.inputKey) (circuitSourceSlope source)
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
      (circuitSourceTable source)
      (fun gate slot active => circuitMaskDirective_record_eq_raw coin.bridgeKey mask rows input source
        coin.inputKey pointKey gate slot active)
      (rawSourceGood_offsets coin source input history good)
    simp only [pipelineGateSchedule, gateProgramRecords, List.flatMap_append, List.pairwise_append] at pairwise
    exact pairwise.1

/-- The valid linked schedule uses the same good source. -/
theorem rawSourceGood_linked (coin : SimulatorCoin) (state : SimulatorState)
    (mask : BaseField) (rows : FieldMacToECMac.Rows) (source : CircuitMaskSample)
    (input : AffineInput) (history : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords history)
    (enc : state.encOracle = coin.oracles.encOracle) (hash : state.hashOracle = coin.oracles.hashOracle)
    (valid : OnCurve input) (good : ¬ rawSourceBad coin source input history) :
    let sample := circuitMaskSampleGarble coin.bridgeKey mask rows input source
    FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (linkedPipelineGateSchedule state sample.curveRequest sample.pointRequests input
        (coin.inputKey.encodeAffine input))) := by
  dsimp only
  rw [circuitMaskSampleGarble_linkedSchedule state coin.bridgeKey mask rows input source coin.inputKey valid,
    enc, hash]
  exact rawSourceGood_pipeline coin state mask rows source input history members valid good

end
end Kriterion.ArgoMAC.Security
