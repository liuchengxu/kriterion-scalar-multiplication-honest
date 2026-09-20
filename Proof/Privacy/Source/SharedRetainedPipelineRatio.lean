import Proof.Privacy.Source.SharedPipelineSourceRatio
import Proof.Privacy.Source.SharedRetainedContext

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance retainedPipelineGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription PMF.uniformOfFintype
set_option maxRecDepth 2048

/-- A complete retained tag satisfies the actual shared full-pipeline source bound. -/
theorem sharedRetainedPipelineSource_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (key : InputMacKey) (state : Shared.Simulator.OracleState)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (nonfixed : SharedNonFixedTranscriptCompatible (reference, rest.encPRFOracle, rest.hashOracle) transcript)
    (pointGood :
      let retained := SharedRetained.retainedSourceContext rest outputKeys input tag key
      ¬ pointBranchCollision retained.1.visible.2 retained.1.rows retained.1.input retained.1.targets retained.2.2)
    (budget : (state.fixedTranscript ++ queries).length ≤ 2 ^ 101)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := retainedFullSource rest tag
    let rows := FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness
    let pointKey := EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) key
    let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value rows input source
    let values := scheduleCommands (pipelineGateSchedule sample.curveRequest sample.pointRequests input
      (key.encodeAffine input) (pointKey.encodeAffine input))
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values) →
    (1 - ((54690772 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
      ((PMF.uniformOfFintype FullCircuitSource) tag * Shared.Simulator.transcriptMass state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
          (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
          {next | PermutationTranscriptMatches next.fixedOracle queries}) ≤
      sharedLinkedHiddenSourceMass rest source tag.1 input (key.encodeAffine input) transcript := by
  dsimp only
  let retained := SharedRetained.retainedSourceContext rest outputKeys input tag key
  have bound := sharedRealSource_pipeline_ratio rest retained.1
    (SharedRetained.retainedSourceContext_linked rest outputKeys input tag key) retained.2
    (fun index => inputKeyLabel key index (!(inputSelectedLabelBit input index)))
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    state queries transcript fixed reference nonfixed pointGood budget
  dsimp only at bound
  have recoveredKey := SharedRetained.retainedSourceContext_key rest outputKeys input tag key
  have recoveredSource := SharedRetained.retainedSourceContext_source rest outputKeys input tag key
  have recoveredLifts := SharedRetained.retainedSourceContext_lifts rest outputKeys input tag complete key
  have recoveredTag := SharedRetained.retainedSourceContext_tag rest outputKeys input tag complete key
  change retained.1.curveKey _ = key at recoveredKey
  change retained.1.source retained.2 = _ at recoveredSource
  change retained.1.lifts retained.2 = tag.1 at recoveredLifts
  change (retained.1.lifts retained.2, sourceCiphertexts (retained.1.source retained.2)) = tag at recoveredTag
  rw [recoveredKey, recoveredTag, recoveredSource, recoveredLifts] at bound
  exact bound

end
end Kriterion.ArgoMAC.Security
