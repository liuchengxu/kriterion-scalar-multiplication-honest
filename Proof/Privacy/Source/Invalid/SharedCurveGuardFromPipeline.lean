import Proof.Privacy.Source.Invalid.SharedCurveFullSourceMass
import Proof.Privacy.Source.Valid.SharedPipelineGlobalRatio

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local irreducible] circuitMaskSampleGarble

private theorem freshPrefix {Index : Type} (history first last : List (PermutationRecord Index Block))
    (fresh : FreshRecordSchedule history (first ++ last)) : FreshRecordSchedule history first := by
  induction first generalizing history with
  | nil => trivial
  | cons head rest ih => exact ⟨fresh.1, ih _ fresh.2⟩

attribute [local irreducible] FreshRecordSchedule Shared.Simulator.commandRecords scheduleCommands
  sharedRetainedPipelineCommands sharedRetainedCurveCommands pipelineGateSchedule

/-- The curve commands form the first part of the complete shared pipeline. -/
theorem sharedPipelineFresh_curve [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule history
      (Shared.Simulator.commandRecords (sharedRetainedPipelineCommands rest keys input key tag))) :
    FreshRecordSchedule history
      (Shared.Simulator.commandRecords (sharedRetainedCurveCommands rest keys input key tag)) := by
  simp only [sharedRetainedPipelineCommands, sharedRetainedCurveCommands, pipelineGateSchedule,
    scheduleCommands, List.flatMap_append, Shared.Simulator.commandRecords, List.map_append] at fresh ⊢
  exact freshPrefix _ _ _ fresh

/-- The pipeline guard supplies the curve guard when the bridge key misses the full transcript. -/
theorem sharedPipelineTagGood_curve [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource)
    (good : SharedPipelineTagGood rest keys table input key state tag)
    (miss : rest.algebraic.field.bridgeKey ∉ transcriptHashInputs (sharedLegacyTranscript transcript)) :
    SharedCurveTagGood rest keys table input key state transcript tag := by
  unfold SharedCurveTagGood
  exact ⟨good.1, good.2.1, miss, good.2.2.1, sharedPipelineFresh_curve rest keys input key tag state.fixedTranscript good.2.2.2⟩

/-- The only extra curve guard failure is a bridge-key query in the complete transcript. -/
theorem sharedCurveTagBad_subset [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (state : Shared.Simulator.OracleState) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource)
    (bad : ¬ SharedCurveTagGood rest keys table input key state transcript tag) :
    ¬ SharedPipelineTagGood rest keys table input key state tag ∨
      rest.algebraic.field.bridgeKey ∈ transcriptHashInputs (sharedLegacyTranscript transcript) := by
  classical
  by_cases good : SharedPipelineTagGood rest keys table input key state tag
  · exact Or.inr (Classical.not_not.mp fun miss => bad (sharedPipelineTagGood_curve rest keys table input key state transcript tag good miss))
  · exact Or.inl good

end
end Kriterion.ArgoMAC.Security
