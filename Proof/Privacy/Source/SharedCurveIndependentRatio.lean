import Proof.Privacy.Source.SharedCurvePipelineRatio
import Proof.Privacy.Source.SharedCurveIndependentMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
local instance curveIndependentRatioFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveIndependentRatioNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual curve-only program fits the guarded independent point-key source. -/
theorem sharedCurveSource_independent_ratio [Fintype Block]
    (bridgeKey : BaseField) (context : SharedRetained.Context)
    (hidden : HiddenPublicSample) (anchor : InputMacKey)
    (rows : FieldMacToECMac.Rows) (state : Shared.Simulator.OracleState)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (pointGood : ¬ pointBranchCollision context.visible.2 context.rows context.input context.targets hidden.2)
    (budget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := context.source hidden
    let curveKey := context.curveKey (SharedRetained.curveUnused anchor)
    let pointKey := (context.curveHidden anchor).pointKey (SharedRetained.curveUnused anchor)
    let sample := circuitMaskSampleGarble bridgeKey context.mask rows context.input source
    let values := scheduleCommands (sample.curveRequest.schedule context.input (curveKey.encodeAffine context.input))
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values) →
    (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
      ((PMF.uniformOfFintype FullCircuitSource) (context.lifts hidden, sourceCiphertexts source) *
        Shared.Simulator.transcriptMass state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {next | PermutationTranscriptMatches next.fixedOracle queries}) ≤
      ∑' unused, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) unused *
        ∑' pointKey, (PMF.uniformOfFintype InputMacKey) pointKey *
          (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
            {fixed | RawGarblingMatches (sourceGatePrescription source
                pointKey (context.curveKey unused) (context.lifts hidden)) (Shared.expandOracle fixed) ∧
              PermutationTranscriptMatches fixed (state.fixedTranscript ++ queries) ∧
                EncSourceGood (context.curveKey unused) pointKey} := by
  dsimp only
  intro fresh
  let source := context.source hidden
  let curveKey := context.curveKey (SharedRetained.curveUnused anchor)
  let pointKey := (context.curveHidden anchor).pointKey (SharedRetained.curveUnused anchor)
  let sample := circuitMaskSampleGarble bridgeKey context.mask rows context.input source
  let values := scheduleCommands (sample.curveRequest.schedule context.input (curveKey.encodeAffine context.input))
  rw [← SharedRetained.curveHidden_independent_average_eq context hidden (state.fixedTranscript ++ queries)]
  let mass := (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) /
    (2 : ENNReal) ^ 128)) * ((PMF.uniformOfFintype FullCircuitSource)
    (context.lifts hidden, sourceCiphertexts source) * Shared.Simulator.transcriptMass state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
        (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
        {next | PermutationTranscriptMatches next.fixedOracle queries})
  calc
    _ = ∑' pads, (PMF.uniformOfFintype (EncPRF.PermutationIndex → Block)) pads * mass := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro pads
      apply mul_le_mul_right
      have bound := sharedCurveSource_pipeline_ratio bridgeKey {context with hiddenPointPads := pads}
        hidden anchor rows state queries pointGood budget
      dsimp only at bound
      have sourceEq : ({context with hiddenPointPads := pads}).source hidden = context.source hidden := by
        unfold SharedRetained.Context.source
        rfl
      have liftsEq : ({context with hiddenPointPads := pads}).lifts hidden = context.lifts hidden := by
        unfold SharedRetained.Context.lifts
        rw [sourceEq]
      rw [sourceEq, liftsEq] at bound
      exact bound fresh

end
end Kriterion.ArgoMAC.Security
