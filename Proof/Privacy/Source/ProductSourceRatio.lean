import Proof.Privacy.Source.Valid.ValidSourceRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

set_option maxRecDepth 4096 in
/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_product_ge
    [Fintype Block]
    (rest : GarblingSourceRest) (rows : FieldMacToECMac.Rows)
    (input : BN254.AffineInput) (source : CircuitMaskSample) (curveKey : InputMacKey)
    (oracleRef : PermutationOracle Pipeline.FixedKeyIndex Block) (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let bridgeKey := rest.algebraic.field.bridgeKey
    let pointKey := EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle bridgeKey) curveKey
    let randomness := {rest.reference with fixedKeyOracle := oracleRef}
    let sample := circuitMaskSampleGarble bridgeKey rest.algebraic.field.curveMask.value rows input source
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
    linkedHiddenSourceMass rest source lifts input (curveKey.encodeAffine input) (before ++ after) := by
  dsimp only
  intro compatible offsetsDistinct programmed historyMembers fresh reference priorFits residualFits
  have ratio := circuitMaskProgrammedSource_mass_ratio rest.algebraic.field.bridgeKey
    rest.algebraic.field.curveMask.value rows input source curveKey
    (EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey)
    circuitBucketWire
    (fun bucket => circuitBucketPad rest.oracleCoin rest.algebraic.field.bridgeKey bucket
      (!(circuitBucketInputBit input bucket)))
    {rest.reference with fixedKeyOracle := oracleRef} state before after
    compatible offsetsDistinct programmed historyMembers fresh reference priorFits residualFits
  dsimp only at ratio
  have labels (hidden : EncPRF.PermutationIndex → Block) :=
    linkedMixedLabels_source rest.oracleCoin rest.algebraic.field.bridgeKey input curveKey hidden
  simp only [GarblingSourceRest.oracleCoin] at labels ratio
  simp_rw [labels] at ratio
  have gates (hidden : EncPRF.PermutationIndex → Block) :=
    linkedSource_gates rest.oracleCoin rest.algebraic.field.bridgeKey
      (inputSelectedLabelBit input) (inputMacCoordinateEquiv (curveKey.encodeAffine input), hidden)
      (circuitGateKey (EncPRF.transformKey rest.encPRFOracle
        (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey) curveKey)
      (circuitSourceSlope source)
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)) (circuitSourceTable source)
  simp only [sourceGatePrescription] at ratio
  simp only [GarblingSourceRest.oracleCoin] at gates
  simp_rw [gates] at ratio
  simpa only [linkedHiddenSourceMass, sourceGatePrescription, realOracleTranscriptCompatible_iff,
    nonFixedTranscriptCompatible_update] using ratio

/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_product_ge_of_reference
    [Fintype Block]
    (rest : GarblingSourceRest) (rows : FieldMacToECMac.Rows)
    (input : BN254.AffineInput) (source : CircuitMaskSample) (curveKey : InputMacKey)
    (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let bridgeKey := rest.algebraic.field.bridgeKey
    let pointKey := EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle bridgeKey) curveKey
    let sample := circuitMaskSampleGarble bridgeKey rest.algebraic.field.curveMask.value rows input source
    let curveMac := curveKey.encodeAffine input
    let pointMac := pointKey.encodeAffine input
    let schedule := pipelineGateSchedule sample.curveRequest sample.pointRequests input curveMac pointMac
    let lifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
    let gates := sourceGatePrescription source pointKey curveKey lifts
    ∀ (_nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
      (_offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
      (_historyMembers : ∀ record, record ∈ state.fixedTranscript ↔
        record ∈ fixedOracleTranscriptRecords before)
      (_fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
      (_reference : TranscriptOracle
        (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ fixedOracleTranscriptRecords after))
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
    linkedHiddenSourceMass rest source lifts input (curveKey.encodeAffine input) (before ++ after) := by
  dsimp only
  intro nonfixed offsetsDistinct historyMembers fresh reference priorFits residualFits
  have matching := programmedReference_matches state.fixedTranscript _ before after historyMembers reference
  have compatible : OracleTranscriptCompatible Garbling.oracleHandler
      {rest.reference with fixedKeyOracle := reference.1} (before ++ after) := by
    rw [realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update]
    exact ⟨matching.1, nonfixed⟩
  exact linkedHiddenSourceMass_product_ge rest rows input source curveKey reference.1 state before after
    compatible offsetsDistinct matching.2 historyMembers fresh reference priorFits residualFits

/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_product_ge_of_nonfixed
    [Fintype Block]
    (rest : GarblingSourceRest) (rows : FieldMacToECMac.Rows)
    (input : BN254.AffineInput) (source : CircuitMaskSample) (curveKey : InputMacKey)
    (state : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let bridgeKey := rest.algebraic.field.bridgeKey
    let pointKey := EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle bridgeKey) curveKey
    let sample := circuitMaskSampleGarble bridgeKey rest.algebraic.field.curveMask.value rows input source
    let curveMac := curveKey.encodeAffine input
    let pointMac := pointKey.encodeAffine input
    let schedule := pipelineGateSchedule sample.curveRequest sample.pointRequests input curveMac pointMac
    let lifts := fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)
    let gates := sourceGatePrescription source pointKey curveKey lifts
    ∀ (_nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
      (_offsetsDistinct : ∀ index, Function.Injective (rawBucketOffset gates index))
      (_historyMembers : ∀ record, record ∈ state.fixedTranscript ↔
        record ∈ fixedOracleTranscriptRecords before)
      (_fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
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
    linkedHiddenSourceMass rest source lifts input (curveKey.encodeAffine input) (before ++ after) := by
  dsimp only
  intro nonfixed offsetsDistinct historyMembers fresh priorFits residualFits
  apply programmed_mass_lower_of_extension
    state _ (fixedOracleTranscriptRecords after) fresh
    (fun mass => (1 - (182 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((∏ index, ((Fintype.card Block : ℝ≥0∞) ^ circuitBucketSize index)⁻¹) *
        fixedTranscriptFactor state.fixedTranscript * mass))
    (sourceScale_zero _ _ _)
  intro reference
  exact linkedHiddenSourceMass_product_ge_of_reference rest rows input source curveKey state before after
    nonfixed offsetsDistinct historyMembers fresh reference priorFits residualFits

end
end Kriterion.ArgoMAC.Security
