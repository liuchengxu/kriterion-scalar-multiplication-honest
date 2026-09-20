import Proof.Privacy.Source.SharedCurveProgramRatio
import Proof.Privacy.Source.SharedCurveKeyEquiv
import Proof.Privacy.Source.SharedQueryBudget
import Proof.Privacy.Programming.SharedCurveCompatibility
import Proof.Privacy.Distribution.SharedProgramExtension

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
local instance curvePipelineKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curvePipelineKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype rawBucketUseFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1

/-- The actual curve-only program fits the guarded independent source at the public query budget. -/
theorem sharedCurveSource_pipeline_ratio [Fintype Block]
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
      ∑' key, (PMF.uniformOfFintype InputMacKey) key *
        (PMF.uniformOfFintype (PermutationOracle Shared.FixedKeyIndex Block)).toOuterMeasure
          {fixedOracle | RawGarblingMatches
            ((context.curveHidden key).gates (hidden, SharedRetained.curveUnused key)) (Shared.expandOracle fixedOracle) ∧
              PermutationTranscriptMatches fixedOracle (state.fixedTranscript ++ queries) ∧
                ¬ SharedRetained.curveHiddenPadBad context key} := by
  dsimp only
  intro fresh
  let source := context.source hidden
  let curveKey := context.curveKey (SharedRetained.curveUnused anchor)
  let pointKey := (context.curveHidden anchor).pointKey (SharedRetained.curveUnused anchor)
  let sample := circuitMaskSampleGarble bridgeKey context.mask rows context.input source
  let values := scheduleCommands (sample.curveRequest.schedule context.input (curveKey.encodeAffine context.input))
  apply Shared.Simulator.commands_mass_lower_of_extension state values queries fresh
    (fun mass => (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) /
      (2 : ENNReal) ^ 128)) * ((PMF.uniformOfFintype FullCircuitSource)
      (context.lifts hidden, sourceCiphertexts source) * Shared.Simulator.transcriptMass state.fixedTranscript * mass))
    (by simp only [mul_zero])
  intro extension
  have gates := SharedRetained.independent_gates (context.curveHidden anchor)
    (hidden, SharedRetained.curveUnused anchor)
  dsimp only at gates
  rw [SharedRetained.curveHidden_source_eq, SharedRetained.curveHidden_lifts_eq] at gates
  have domains : SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords values) =
      sharedCurveDomains ((context.curveHidden anchor).gates (hidden, SharedRetained.curveUnused anchor)) (sharedCircuitSelected context.input) := by
    rw [gates]
    funext index
    exact sharedCurveRecords_domains bridgeKey context.mask rows context.input
      source curveKey pointKey index
  have activeFits (index : Shared.FixedKeyIndex) := sharedCurveRecords_domainCount_le
    bridgeKey context.mask rows context.input source curveKey pointKey index
  have prefixBudget : state.fixedTranscript.length ≤ 2 ^ 101 := by
    rw [List.length_append] at budget
    omega
  refine SharedRetained.curveHidden_program_ratio context hidden anchor pointGood
    (context.lifts hidden, sourceCiphertexts source) state values queries fresh extension domains ?_ activeFits ?_ ?_
  · intro gate slot curve selected
    rw [gates]
    apply sharedCurveSourceSchedule_active bridgeKey context.mask rows context.input
      source curveKey pointKey extension.1 _ gate slot curve selected
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
