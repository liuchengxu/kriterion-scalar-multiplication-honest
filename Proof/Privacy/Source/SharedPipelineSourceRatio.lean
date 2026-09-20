import Proof.Privacy.Source.SharedRealProgramRatio
import Proof.Privacy.Source.SharedQueryBudget
import Proof.Privacy.Programming.SharedScheduleBound
import Proof.Privacy.Distribution.SharedProgramExtension

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual full pipeline needs only source goodness, freshness, and the public query budget. -/
theorem sharedRealSource_pipeline_ratio [Fintype Block]
    (rest : GarblingSourceRest) (context : SharedRetained.Context)
    (linked : context.Linked rest.oracleCoin rest.algebraic.field.bridgeKey)
    (hidden : HiddenPublicSample) (anchor : EncPRF.PermutationIndex → Block)
    (rows : FieldMacToECMac.Rows) (state : Shared.Simulator.OracleState)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (reference, rest.encPRFOracle, rest.hashOracle) transcript)
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (budget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := context.source hidden
    let curveKey := context.curveKey anchor
    let pointKey := EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey
    let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey context.mask rows context.input source
    let values := scheduleCommands (pipelineGateSchedule sample.curveRequest sample.pointRequests context.input
      (curveKey.encodeAffine context.input) (pointKey.encodeAffine context.input))
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values) →
    (1 - ((54690772 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
      ((PMF.uniformOfFintype FullCircuitSource) (context.lifts hidden, sourceCiphertexts source) *
        Shared.Simulator.transcriptMass state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {next | PermutationTranscriptMatches next.fixedOracle queries}) ≤
      sharedLinkedHiddenSourceMass rest source (context.lifts hidden) context.input
        (curveKey.encodeAffine context.input) transcript := by
  dsimp only
  intro fresh
  let source := context.source hidden
  let curveKey := context.curveKey anchor
  let pointKey := EncPRF.transformKey rest.encPRFOracle
    (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) curveKey
  let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey context.mask rows context.input source
  let values := scheduleCommands (pipelineGateSchedule sample.curveRequest sample.pointRequests context.input
    (curveKey.encodeAffine context.input) (pointKey.encodeAffine context.input))
  apply Shared.Simulator.commands_mass_lower_of_extension state values queries fresh
    (fun mass => (1 - ((54690772 + (364 * (state.fixedTranscript ++ queries).length : Nat)) /
      (2 : ENNReal) ^ 128)) * ((PMF.uniformOfFintype FullCircuitSource)
      (context.lifts hidden, sourceCiphertexts source) * Shared.Simulator.transcriptMass state.fixedTranscript * mass))
    (by simp only [mul_zero])
  intro extension
  have labels : context.activeCurveLabels = inputMacCoordinateEquiv (curveKey.encodeAffine context.input) := by
    have selected := congrArg Prod.fst
      ((selectedKeyLabelsEquiv (inputSelectedLabelBit context.input)).apply_symm_apply
        (context.activeCurveLabels, anchor))
    exact selected.symm.trans ((selectedKeyLabels_public_iff context.input curveKey _).mpr rfl)
  have gates := SharedRetained.linked_gates context rest.oracleCoin rest.algebraic.field.bridgeKey linked
    (hidden, anchor)
  dsimp only [GarblingSourceRest.oracleCoin, SharedRetained.Context.lifts] at gates
  have domains : SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values) =
      sharedActiveDomains (context.gates (hidden, anchor)) (sharedCircuitSelected context.input) := by
    rw [gates]
    funext index
    exact sharedCircuitRecords_domains rest.algebraic.field.bridgeKey context.mask rows context.input
      source curveKey pointKey index
  have activeFits (index : Shared.FixedKeyIndex) := sharedCircuitRecords_domainCount_le
    rest.algebraic.field.bridgeKey context.mask rows context.input source curveKey pointKey index
  have prefixBudget : state.fixedTranscript.length ≤ 2 ^ 101 := by
    rw [List.length_append] at budget
    omega
  refine sharedRealSource_program_ratio rest context linked hidden _ labels anchor pointGood
    (context.lifts hidden, sourceCiphertexts source) state values queries transcript fixed fresh extension
    ((sharedNonFixedTranscriptCompatible_fixed extension.1 reference rest.encPRFOracle rest.hashOracle transcript).mpr nonfixed)
    domains ?_ activeFits ?_ ?_
  · intro gate slot selected
    rw [gates]
    apply sharedSourceSchedule_active rest.algebraic.field.bridgeKey context.mask rows context.input
      source curveKey pointKey extension.1 _ gate slot selected
    dsimp only
    intro record member
    exact extension.2 record (List.mem_append_left queries
      ((SharedQueryCounts.mem_programRecordHistory_iff _ _ _).mpr (Or.inl member)))
  · intro index
    exact (Nat.add_le_add_right (activeFits index) _).trans
      (sharedQueryBudget_fits state.fixedTranscript (fun _ => ∅) prefixBudget index).1
  · intro index
    exact (sharedQueryBudget_fits (state.fixedTranscript ++ queries) _ budget index).2

end
end Kriterion.ArgoMAC.Security
