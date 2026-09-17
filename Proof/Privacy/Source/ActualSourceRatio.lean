import Proof.Privacy.Source.RealSourceSum
import Proof.Privacy.Source.ActualAdaptiveRatio
import Proof.Privacy.Source.FullCircuitSourceDensity

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1 instDecidableEqRawCircuitGate_1 rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype transcriptOracleFintype

/-- A positive programmed-query event supplies its own transcript extension. -/
theorem programGateSchedule_extension_of_mass_ne_zero [Fintype Block]
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (positive : ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} ≠ 0) :
    Nonempty (TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries)) := by
  have intersects : ¬ Disjoint
      (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => programGateSchedule {state with fixedOracle := oracle.1} schedule)).support)
      {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} := by
    rwa [← PMF.toOuterMeasure_apply_eq_zero_iff]
  obtain ⟨programmed, supported, matching⟩ := Set.not_disjoint_iff.mp intersects
  simp only [PMF.mem_support_map_iff] at supported
  obtain ⟨oracle, _, rfl⟩ := supported
  rw [programGateSchedule_state state schedule fresh oracle] at matching
  let extended := programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh oracle
  exact ⟨⟨extended.1, (permutationTranscriptMatches_append _ _ _).mpr ⟨extended.2, matching⟩⟩⟩

/-- A zero query mass needs no extension witness. -/
theorem programmed_mass_lower_of_extension [Fintype Block]
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (lower : ℝ≥0∞ → ℝ≥0∞) (atZero : lower 0 = 0) (target : ℝ≥0∞)
    (bound : ∀ (_reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries)),
      lower (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤ target) :
    lower (((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries}) ≤ target := by
  by_cases empty : ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
      (fun oracle => programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} = 0
  · rw [empty, atZero]
    exact bot_le
  · exact bound (Classical.choice (programGateSchedule_extension_of_mass_ne_zero state schedule queries fresh empty))

set_option maxRecDepth 4096 in
/-- The actual valid schedule gives the retained hidden-source mass with exact source density. -/
theorem linkedHiddenSourceMass_programmed_ge
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
      (((PMF.uniformOfFintype FullCircuitSource) (lifts, sourceCiphertexts source)) *
        fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
            {programmed | PermutationTranscriptMatches programmed.fixedOracle
              (fixedOracleTranscriptRecords after)}) ≤
    linkedHiddenSourceMass rest source lifts input (curveKey.encodeAffine input) (before ++ after) := by
  dsimp only
  intro compatible offsetsDistinct programmed historyMembers fresh reference priorFits residualFits
  rw [fullCircuitSource_uniform_mass]
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

end
end Kriterion.ArgoMAC.Security
