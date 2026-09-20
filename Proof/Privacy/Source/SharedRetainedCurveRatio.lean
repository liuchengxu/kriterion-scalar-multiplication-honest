import Proof.Privacy.Source.SharedLinkedCurveRatio
import Proof.Privacy.Source.SharedRetainedContext

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography SharedQueryCounts
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance retainedCurveGateDecidableEq : DecidableEq RawCircuitGate := fun a b => FinEnum.decEq a b
set_option maxRecDepth 2048
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords
  circuitMaskSampleGarble sourceGatePrescription PMF.uniformOfFintype

/-- This anchor stores the actual unused labels in the false branch. -/
def retainedCurveAnchor (input : AffineInput) (key : InputMacKey) : InputMacKey :=
  (selectedKeyLabelsEquiv (fun _ => true)).symm
    (fun _ => 0, fun index => inputKeyLabel key index (!(inputSelectedLabelBit input index)))

/-- The anchor recovers every actual unused label. -/
theorem retainedCurveAnchor_unused (input : AffineInput) (key : InputMacKey) :
    SharedRetained.curveUnused (retainedCurveAnchor input key) =
      fun index => inputKeyLabel key index (!(inputSelectedLabelBit input index)) := by
  exact congrArg Prod.snd ((selectedKeyLabelsEquiv (fun _ => true)).apply_symm_apply _)

/-- A complete retained tag satisfies the actual curve-only linked source bound. -/
theorem sharedRetainedCurveSource_linked_ratio [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (outputKeys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (tag : FullCircuitSource) (complete : FullSourceComplete tag.1)
    (key : InputMacKey) (state : Shared.Simulator.OracleState)
    (queries : List (PermutationRecord Shared.FixedKeyIndex Block))
    (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (fixed : (sharedFixedTranscriptRecords transcript).Perm (state.fixedTranscript ++ queries))
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (sharedLegacyTranscript transcript))
    (pointGood :
      let retained := SharedRetained.retainedSourceContext rest outputKeys input tag key
      ¬ pointBranchCollision retained.1.visible.2 retained.1.rows retained.1.input retained.1.targets retained.2.2)
    (budget : Nat) (small : budget ≤ 2 ^ 101) (lengthBound : transcript.length ≤ budget)
    [Nonempty (TranscriptOracle state.fixedTranscript)] :
    let source := retainedFullSource rest tag
    let rows := FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness
    let sample := circuitMaskSampleGarble rest.algebraic.field.bridgeKey rest.algebraic.field.curveMask.value rows input source
    let values := scheduleCommands (sample.curveRequest.schedule input (key.encodeAffine input))
    FreshRecordSchedule state.fixedTranscript (Shared.Simulator.commandRecords values) →
    ((1 - ((4 * budget : Nat) : ENNReal) / Fintype.card Block) *
      encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript transcript))) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        if SharedNonFixedTranscriptCompatible (state.fixedOracle, rest.encPRFOracle, hash) transcript then
          (1 - ((54691280 + (364 * (state.fixedTranscript ++ queries).length : Nat)) / (2 : ENNReal) ^ 128)) *
            ((PMF.uniformOfFintype FullCircuitSource) tag *
              Shared.Simulator.transcriptMass state.fixedTranscript *
              ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map
                (fun oracle => Shared.Simulator.commands {state with fixedOracle := oracle.1} values)).toOuterMeasure
                {next | PermutationTranscriptMatches next.fixedOracle queries}) else 0) ≤
      ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
            sharedLinkedHiddenSourceMass {rest with encPRFOracle := enc, hashOracle := hash}
              source tag.1 input (key.encodeAffine input) transcript := by
  dsimp only
  let retained := SharedRetained.retainedSourceContext rest outputKeys input tag key
  have bound := sharedCurveSource_linked_ratio rest retained.1 retained.2 (retainedCurveAnchor input key)
    (FieldMacToECMac.rowsForOutputKeys outputKeys rest.algebraic.point.pointRandomness)
    state queries transcript fixed miss pointGood budget small lengthBound
  dsimp only at bound
  rw [retainedCurveAnchor_unused] at bound
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
