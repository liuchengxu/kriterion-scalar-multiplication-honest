import Proof.Privacy.Source.Valid.ValidSourceKernel
import Proof.Privacy.Source.FullSourceGood

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local irreducible] linkedHiddenSourceMass
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- A zero query mass gives a zero scaled source mass. -/
theorem sourceScale_zero (a b c : ℝ≥0∞) : a * (b * c * 0) = 0 := by
  rw [mul_zero, mul_zero]

/-- An extended programmed oracle retains the prefix and the selected equations. -/
theorem programmedReference_matches
    (history records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (members : ∀ record, record ∈ history ↔ record ∈ fixedOracleTranscriptRecords before)
    (reference : TranscriptOracle (programRecordHistory history records ++ fixedOracleTranscriptRecords after)) :
    PermutationTranscriptMatches reference.1 (fixedOracleTranscriptRecords (before ++ after)) ∧
    PermutationTranscriptMatches reference.1 records := by
  have retained := (permutationTranscriptMatches_append _ _ _).mp reference.2
  constructor
  · rw [fixedOracleTranscriptRecords_append, permutationTranscriptMatches_append]
    refine ⟨?_, retained.2⟩
    intro record member
    exact retained.1 record ((mem_programRecordHistory_iff history records record).mpr
      (Or.inr ((members record).mpr member)))
  · intro record member
    exact retained.1 record ((mem_programRecordHistory_iff history records record).mpr (Or.inl member))

/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_programmed_ge_of_reference
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
      (((PMF.uniformOfFintype FullCircuitSource) (lifts, sourceCiphertexts source)) *
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
  exact linkedHiddenSourceMass_programmed_ge rest rows input source curveKey reference.1 state before after
    compatible offsetsDistinct matching.2 historyMembers fresh reference priorFits residualFits

/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_programmed_ge_of_nonfixed
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
      (((PMF.uniformOfFintype FullCircuitSource) (lifts, sourceCiphertexts source)) *
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
      (((PMF.uniformOfFintype FullCircuitSource)
        ((fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate)), sourceCiphertexts source)) *
        fixedTranscriptFactor state.fixedTranscript * mass))
    (sourceScale_zero _ _ _)
  intro reference
  exact linkedHiddenSourceMass_programmed_ge_of_reference rest rows input source curveKey state before after
    nonfixed offsetsDistinct historyMembers fresh reference priorFits residualFits

end
end Kriterion.ArgoMAC.Security
