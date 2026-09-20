import Proof.Privacy.Source.Valid.SharedPipelineGlobalRatio
import Proof.Privacy.Transcript.SharedPrefixProgrammed
import Proof.Privacy.Source.Valid.ValidSourceNormalization

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance pipelineEventKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance pipelineEventKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- This event keeps the selected MAC and both actual shared recording phases. -/
def sharedPipelineTagEvent [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource) :
    Set ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :=
  {sample | sample.2.encodeAffine input = key.encodeAffine input ∧
    SharedPipelineTagGood rest keys table input key
      (transcriptFinalState idealOracleHandler initial before) tag ∧
    OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := sample.1} before ∧
    OracleTranscriptCompatible idealOracleHandler
      (Shared.Simulator.commands
        (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
        (sharedRetainedPipelineCommands rest keys input key tag)) after}

/-- The selected MAC and compatible prefix give the exact conditional full-pipeline mass. -/
theorem sharedPipelineTagEvent_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, initial.hashOracle) after)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedPipelineTagEvent rest keys table input key initial before after tag) =
    if SharedPipelineTagGood rest keys table input key
      (transcriptFinalState idealOracleHandler initial before) tag then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
        (Shared.Simulator.transcriptMass (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
          ((PMF.uniformOfFintype
            (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map
              (fun oracle => Shared.Simulator.commands
                {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
                (sharedRetainedPipelineCommands rest keys input key tag))).toOuterMeasure
                  {programmed | PermutationTranscriptMatches programmed.fixedOracle (sharedFixedTranscriptRecords after)})
    else 0 := by
  let kept := SharedPipelineTagGood rest keys table input key
    (transcriptFinalState idealOracleHandler initial before) tag
  let event := fun oracle : PermutationOracle Shared.FixedKeyIndex Block =>
    OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
      OracleTranscriptCompatible idealOracleHandler
        (Shared.Simulator.commands
          (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
          (sharedRetainedPipelineCommands rest keys input key tag)) after
  by_cases good : kept
  · have same : sharedPipelineTagEvent rest keys table input key initial before after tag =
        {sample | sample.2.encodeAffine input = key.encodeAffine input ∧ event sample.1} := by
      ext sample
      exact and_congr_right fun _ => and_iff_right good
    rw [same]
    have labelsLaw := uniform_selectedMac_event_mass input key {oracle | event oracle}
    simp only [Set.mem_setOf_eq] at labelsLaw
    rw [labelsLaw, if_pos good]
    apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ * ·)
    exact sharedIdealPrefixProgrammed_fixed_mass initial before after
      (sharedRetainedPipelineCommands rest keys input key tag) empty compatible nonfixed
  · rw [if_neg good]
    have emptyEvent : sharedPipelineTagEvent rest keys table input key initial before after tag = ∅ := by
      ext sample
      simp only [sharedPipelineTagEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      exact iff_false_intro fun member => good member.2.1
    rw [emptyEvent]
    simp

end
end Kriterion.ArgoMAC.Security
