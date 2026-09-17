import Proof.Privacy.Transcript.AdaptiveGameRatio
import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.ArgoMAC.Security

open Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype


/-- The fixed records preserve transcript concatenation. -/
theorem fixedOracleTranscriptRecords_append
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    fixedOracleTranscriptRecords (before ++ after) =
      fixedOracleTranscriptRecords before ++ fixedOracleTranscriptRecords after := by
  induction before with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      cases request <;>
        simp only [List.cons_append, fixedOracleTranscriptRecords, inductionHypothesis]

/-- The recording handler keeps the complete fixed query history. -/
theorem idealTranscriptFinal_fixedHistory (state : SimulatorState)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state transcript) :
    (transcriptFinalState idealOracleHandler state transcript).fixedTranscript =
      (fixedOracleTranscriptRecords transcript).reverse ++ state.fixedTranscript := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      simp only [idealOracleHandler] at inductionHypothesis
      cases request <;>
        simp only [OracleTranscriptCompatible, idealOracleHandler, oracleHandlerFor] at compatible
      all_goals
        simp only [transcriptFinalState, idealOracleHandler, oracleHandlerFor]
        rw [inductionHypothesis _ compatible.2]
        simp only [fixedOracleTranscriptRecords, recordFixed, recordEnc, recordHash,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        try rw [compatible.1]

/-- Equal recorded domain sets give equal residual counts. -/
theorem residualFixedQueryDomain_card_congr [Fintype Block]
    (first second : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (covered : Pipeline.FixedKeyIndex → Set Block)
    (members : ∀ record, record ∈ first ↔ record ∈ second) (index : Pipeline.FixedKeyIndex) :
    Fintype.card (ResidualFixedQueryDomain first covered index) =
      Fintype.card (ResidualFixedQueryDomain second covered index) := by
  classical
  apply Fintype.card_congr
  exact {
    toFun query := ⟨⟨query.1.1, by
      obtain ⟨record, member, equal⟩ := query.1.2
      exact ⟨record, (members record).mp member, equal⟩⟩, query.2⟩
    invFun query := ⟨⟨query.1.1, by
      obtain ⟨record, member, equal⟩ := query.1.2
      exact ⟨record, (members record).mpr member, equal⟩⟩, query.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }

/-- The actual schedule removes exactly the selected replay domains. -/
theorem pipelineGateProgramRecords_residualCount [Fintype Block]
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : BN254.AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BN254.BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (historyMembers : ∀ record, record ∈ history ↔ record ∈ fixedOracleTranscriptRecords before)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (ResidualFixedQueryDomain (history ++ fixedOracleTranscriptRecords after)
      (programmedDomains (gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac))) index) =
    circuitResidualQueryCount (circuitRawGatePrescription keys slopes lifts tables)
      (circuitBucketInputBit input) (circuitBucketInputLabel curveInputMac pointInputMac)
      (before ++ after) index := by
  classical
  have domains : programmedDomains (gateProgramRecords
      (pipelineGateSchedule curve points input curveInputMac pointInputMac)) =
      rawActiveDomains (circuitRawGatePrescription keys slopes lifts tables)
        (circuitBucketInputBit input) (circuitBucketInputLabel curveInputMac pointInputMac) := by
    funext bucket
    exact pipelineGateProgramRecords_domains curve points input curveInputMac pointInputMac
      keys slopes lifts tables bucket
  rw [domains, circuitResidualQueryCount]
  apply residualFixedQueryDomain_card_congr
  intro record
  rw [fixedOracleTranscriptRecords_append before after]; simp only [List.mem_append, historyMembers]
/-- The actual pipeline schedule supplies both count maps in the circuit ratio. -/
theorem actualPipelineProgrammedSource_mass_ratio
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (curve : CurveGateRequest) (points : PointGateRequests)
    (input : BN254.AffineInput) (curveInputMac pointInputMac : InputMac)
    (keys : RawCircuitGate → BitAdaptor.Key) (slopes : RawCircuitGate → BN254.BaseField)
    (lifts : RawCircuitGate → FullHashLift) (tables : RawCircuitGate → BitAdaptor.Table)
    (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after))
    (offsetsDistinct : ∀ index, Function.Injective
      (rawBucketOffset (circuitRawGatePrescription keys slopes lifts tables) index))
    (recordLaw : ∀ gate slot,
      rawSlotBranch slot =
        (actualCircuitDirective curve points input curveInputMac pointInputMac gate).bit →
      (actualCircuitDirective curve points input curveInputMac pointInputMac gate).slotRecord slot =
        (circuitRawGatePrescription keys slopes lifts tables gate).slotRecord slot)
    (programmed : PermutationTranscriptMatches randomness.fixedKeyOracle (gateProgramRecords
      (pipelineGateSchedule curve points input curveInputMac pointInputMac)))
    (state : SimulatorState)
    (historyMembers : ∀ record, record ∈ state.fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords before)
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords
      (pipelineGateSchedule curve points input curveInputMac pointInputMac)))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords
        (pipelineGateSchedule curve points input curveInputMac pointInputMac)) ++
          fixedOracleTranscriptRecords after))
    (priorFits : ∀ index, circuitBucketSize index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, circuitBucketSize index +
      circuitResidualQueryCount (circuitRawGatePrescription keys slopes lifts tables)
        (circuitBucketInputBit input) (circuitBucketInputLabel curveInputMac pointInputMac)
        (before ++ after) index ≤ Fintype.card Block) :
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1}
            (pipelineGateSchedule curve points input curveInputMac pointInputMac))).toOuterMeasure
              {programmed | PermutationTranscriptMatches programmed.fixedOracle
                (fixedOracleTranscriptRecords after)}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels (circuitRawGatePrescription keys slopes lifts tables)
            (rawMixedLabels (circuitBucketInputBit input)
              (circuitBucketInputLabel curveInputMac pointInputMac) wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} (before ++ after)} := by
  apply circuitProgrammedSource_mass_ratio keys slopes lifts tables (circuitBucketInputBit input)
    wire shift (circuitBucketInputLabel curveInputMac pointInputMac) randomness (before ++ after)
    compatible offsetsDistinct _ state
    (pipelineGateSchedule curve points input curveInputMac pointInputMac)
    (fixedOracleTranscriptRecords after) fresh reference _ _ priorFits residualFits
  · exact pipelineGateProgramRecords_referenceActive curve points input curveInputMac pointInputMac
      keys slopes lifts tables recordLaw randomness.fixedKeyOracle programmed
  · exact pipelineGateProgramRecords_domainCount curve points input curveInputMac pointInputMac
      keys slopes lifts tables
  · exact pipelineGateProgramRecords_residualCount curve points input curveInputMac pointInputMac
      keys slopes lifts tables state.fixedTranscript before after historyMembers
/-- An initially empty fixed history contains exactly the selected prefix records. -/
theorem idealTranscriptFinal_fixedHistory_members (state : SimulatorState)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler state transcript)
    (empty : state.fixedTranscript = [])
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ (transcriptFinalState idealOracleHandler state transcript).fixedTranscript ↔
      record ∈ fixedOracleTranscriptRecords transcript := by
  rw [idealTranscriptFinal_fixedHistory state transcript compatible, empty]
  simp only [List.append_nil, List.mem_reverse]

/-- The circuit handler changes only its retained oracle state. -/
theorem circuitTranscriptFinalState (state : CircuitSimulatorState)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    transcriptFinalState circuitSimulatorOracleHandler state transcript =
      {state with oracle := transcriptFinalState idealOracleHandler state.oracle transcript} := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      simp only [transcriptFinalState, circuitSimulatorOracleHandler, inductionHypothesis]

/-- The circuit prefix gives exactly the recorded ideal oracle answers. -/
theorem circuitOracleTranscriptCompatible_iff (state : CircuitSimulatorState)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    OracleTranscriptCompatible circuitSimulatorOracleHandler state transcript ↔
      OracleTranscriptCompatible idealOracleHandler state.oracle transcript := by
  induction transcript generalizing state with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨request, answer⟩
      simp only [OracleTranscriptCompatible, circuitSimulatorOracleHandler, inductionHypothesis]
/-- Every residual bucket count fits the complete external query count. -/
theorem circuitResidualQueryCount_le_length [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (gates : RawCircuitGate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (index : Pipeline.FixedKeyIndex) :
    circuitResidualQueryCount gates selected publicLabel transcript index ≤ transcript.length := by
  classical
  apply (Fintype.card_le_of_injective
    (fun query : ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
      (rawActiveDomains gates selected publicLabel) index => query.1) Subtype.val_injective).trans
  apply le_trans _ (fixedExternalQueryCount_le transcript)
  exact Finset.single_le_sum
    (f := fun bucket => Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) bucket))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)

/-- The circuit and residual query counts fit when the total transcript fits. -/
theorem circuitResidualQueryCounts_fit [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (gates : RawCircuitGate → RawGatePrescription) (selected : RawLabelBucket → Bool)
    (publicLabel : RawLabelBucket → Block)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (fits : 91 + transcript.length ≤ Fintype.card Block) (index : Pipeline.FixedKeyIndex) :
    circuitBucketSize index + circuitResidualQueryCount gates selected publicLabel transcript index ≤
      Fintype.card Block :=
  (Nat.add_le_add (circuitBucketSize_le index)
    (circuitResidualQueryCount_le_length gates selected publicLabel transcript index)).trans fits

/-- The retained mask source supplies the actual record equality in the circuit ratio. -/
theorem circuitMaskProgrammedSource_mass_ratio
    {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block] [Fintype Pipeline.FixedKeyIndex]
    (bridgeKey mask : BN254.BaseField) (rows : FieldMacToECMac.Rows)
    (input : BN254.AffineInput) (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (wire : RawLabelBucket → Wire) (shift : RawLabelBucket → Block)
    (randomness : Garbling.Randomness) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let curveMac := curveKey.encodeAffine input
    let pointMac := pointKey.encodeAffine input
    let schedule := pipelineGateSchedule sample.curveRequest sample.pointRequests input curveMac pointMac
    let lifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
    let gates := sourceGatePrescription source pointKey curveKey lifts
    ∀ (_compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after))
      (_offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
      (_programmed : PermutationTranscriptMatches randomness.fixedKeyOracle (gateProgramRecords schedule))
      (_historyMembers : ∀ record, record ∈ state.fixedTranscript ↔
        record ∈ fixedOracleTranscriptRecords before)
      (_fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
      (_reference : TranscriptOracle
        (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++
          fixedOracleTranscriptRecords after))
      (_priorFits : ∀ index, circuitBucketSize index +
        Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
      (_residualFits : ∀ index, circuitBucketSize index +
        circuitResidualQueryCount gates (circuitBucketInputBit input)
          (circuitBucketInputLabel curveMac pointMac) (before ++ after) index ≤ Fintype.card Block),
    (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle
              (fixedOracleTranscriptRecords after)}) ≤
    (PMF.uniformOfFintype
      ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
        {sample | RawGarblingMatches
          (rawGatesWithLabels gates
            (rawMixedLabels (circuitBucketInputBit input)
              (circuitBucketInputLabel curveMac pointMac) wire shift sample.2)) sample.1 ∧
          OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with fixedKeyOracle := sample.1} (before ++ after)} := by
  dsimp only
  intro compatible offsetsDistinct programmed historyMembers fresh reference priorFits residualFits
  apply actualPipelineProgrammedSource_mass_ratio
    (circuitMaskSampleGarble bridgeKey mask rows input source).curveRequest
    (circuitMaskSampleGarble bridgeKey mask rows input source).pointRequests input
    (curveKey.encodeAffine input) (pointKey.encodeAffine input)
    (circuitGateKey pointKey curveKey) (circuitSourceSlope source)
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    (circuitSourceTable source) wire shift randomness before after compatible offsetsDistinct
    _ programmed state historyMembers fresh reference priorFits residualFits
  exact circuitMaskDirective_record_eq_raw bridgeKey mask rows input source curveKey pointKey

end
end Kriterion.ArgoMAC.Security
