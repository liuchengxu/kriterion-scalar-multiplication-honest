import Proof.Privacy.Source.Valid.SharedPipelineSourceView
import Proof.Privacy.Source.SharedSourcePrefixReference
import Proof.Privacy.Source.Valid.SharedPipelineEventMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The pipeline guard depends on the recorded history and the selected MAC. -/
theorem sharedPipelineTagGood_history [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (first second : Shared.Simulator.OracleState) (tag : FullCircuitSource)
    (same : first.fixedTranscript = second.fixedTranscript) :
    SharedPipelineTagGood rest keys table input key first tag ↔
      SharedPipelineTagGood rest keys table input key second tag := by
  unfold SharedPipelineTagGood
  rw [same]

/-- The valid tag event is the exact selected-view source event. -/
theorem sharedPipelineTagEvent_iff_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource) (labels : Garbling.Labels)
    (valid : OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac)
    (compatible : OracleTranscriptCompatible idealOracleHandler (sharedSourcePrefixReference reference rest) before)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :
    sample ∈ sharedPipelineTagEvent rest keys table input key
      (sharedSourcePrefixReference reference rest) before after tag ↔
    let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
    let state := transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) before
    SharedPipelineTagGood rest keys table input sample.2 state tag ∧
    OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) before ∧
    sourceInputLabels data input = labels ∧
    OracleTranscriptCompatible idealOracleHandler
      (sharedProgramSelectedGateView state input (sample.2.encodeAffine input)
        (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
          rest.algebraic.field.curveMask.value
          (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
          input (retainedFullSource rest tag)) input)) after := by
  let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
  let initial := sharedInitialSourceOracle data
  let state := transcriptFinalState idealOracleHandler initial before
  have initialEq : {sharedSourcePrefixReference reference rest with fixedOracle := sample.1} = initial := by
    simp only [sharedSourcePrefixReference, initial, data, sharedInitialSourceOracle, Shared.restrict_expand]
  have enc : state.encOracle = rest.encPRFOracle := (sharedIdealTranscriptFinal_oracles initial before).2.1
  have hash : state.hashOracle = rest.hashOracle := (sharedIdealTranscriptFinal_oracles initial before).2.2
  have labelsEq : sourceInputLabels data input = labels ↔ sample.2.encodeAffine input = key.encodeAffine input := by
    cases labels
    dsimp only at bits mac
    simp only [sourceInputLabels, Garbling.Labels.mk.injEq, ← mac, ← bits, true_and, data]
  change _ ↔ SharedPipelineTagGood rest keys table input sample.2 state tag ∧
    OracleTranscriptCompatible idealOracleHandler initial before ∧ sourceInputLabels data input = labels ∧ _
  rw [sharedValidSourceView_program rest keys input sample.2 tag state valid enc hash, labelsEq]
  simp only [sharedPipelineTagEvent, Set.mem_setOf_eq, initialEq]
  have histories (supported : OracleTranscriptCompatible idealOracleHandler initial before) :
      (transcriptFinalState idealOracleHandler (sharedSourcePrefixReference reference rest) before).fixedTranscript =
        state.fixedTranscript := by
    rw [sharedIdealTranscriptFinal_fixedHistory _ _ compatible,
      sharedIdealTranscriptFinal_fixedHistory _ _ supported]
    rfl
  constructor
  · rintro ⟨same, good, first, last⟩
    have goodKey := (sharedPipelineTagGood_rekey rest keys table input sample.2 key _ tag same).mpr good
    refine ⟨(sharedPipelineTagGood_history rest keys table input sample.2 _ state tag (histories first)).mp goodKey,
      first, same, ?_⟩
    rw [sharedRetainedPipelineCommands_rekey rest keys input sample.2 key tag same]
    exact last
  · rintro ⟨good, first, same, last⟩
    have goodHistory := (sharedPipelineTagGood_history rest keys table input sample.2 _ state tag (histories first)).mpr good
    refine ⟨same, (sharedPipelineTagGood_rekey rest keys table input sample.2 key _ tag same).mp goodHistory,
      first, ?_⟩
    rw [← sharedRetainedPipelineCommands_rekey rest keys input sample.2 key tag same]
    exact last

end
end Kriterion.ArgoMAC.Security
