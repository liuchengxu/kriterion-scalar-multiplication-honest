import Proof.Privacy.Source.Valid.SharedPipelineEventMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineNonfixedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelineNonfixedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Every retained pipeline event satisfies both nonfixed transcript phases. -/
theorem sharedPipelineTagEvent_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (member : sample ∈ sharedPipelineTagEvent rest keys table input key initial before after tag) :
    SharedNonFixedTranscriptCompatible (initial.fixedOracle, initial.encOracle, initial.hashOracle)
      (before ++ after) := by
  have first := (sharedPublicTranscriptCompatible_iff _ before).mp
    ((sharedIdealTranscriptCompatible_iff _ before).mp member.2.2.1)
  have second := (sharedPublicTranscriptCompatible_iff _ after).mp
    ((sharedIdealTranscriptCompatible_iff _ after).mp member.2.2.2)
  have others := Shared.Simulator.commands_other
    (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
    (sharedRetainedPipelineCommands rest keys input key tag)
  have final := sharedIdealTranscriptFinal_oracles {initial with fixedOracle := sample.1} before
  rw [others.1, others.2, final.2.1, final.2.2] at second
  exact (sharedNonFixedTranscriptCompatible_append _ before after).mpr
    ⟨(sharedNonFixedTranscriptCompatible_fixed _ initial.fixedOracle _ _ before).mp first.2,
      (sharedNonFixedTranscriptCompatible_fixed _ initial.fixedOracle _ _ after).mp second.2⟩

/-- An incompatible nonfixed transcript has zero retained pipeline-event mass. -/
theorem sharedPipelineTagEvent_zero_of_nonfixed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (nonfixed : ¬ SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, initial.hashOracle) (before ++ after)) :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedPipelineTagEvent rest keys table input key initial before after tag) = 0 := by
  have empty : sharedPipelineTagEvent rest keys table input key initial before after tag = ∅ := by
    ext sample
    exact iff_false_intro fun member => nonfixed
      (sharedPipelineTagEvent_nonfixed rest keys table input key initial before after tag sample member)
  rw [empty]
  simp


end
end Kriterion.ArgoMAC.Security
