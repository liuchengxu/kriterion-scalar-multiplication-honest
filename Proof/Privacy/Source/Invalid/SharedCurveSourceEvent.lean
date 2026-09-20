import Proof.Privacy.Source.Invalid.SharedCurveSourceView
import Proof.Privacy.Source.Invalid.SharedCurveEventReference
import Proof.Privacy.Source.SharedSourcePrefixReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The retained source state uses exactly the sampled shared fixed oracle. -/
theorem sharedInitialSourceOracle_sample (reference : Shared.Simulator.OracleState)
    (rest : GarblingSourceRest) (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :
    sharedInitialSourceOracle ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩ =
      {sharedSourcePrefixReference reference rest with fixedOracle := sample.1} := by
  simp only [sharedInitialSourceOracle, sharedSourcePrefixReference, Shared.restrict_expand]

/-- The selected source view gives the exact shared curve tag event. -/
theorem sharedCurveTagEvent_iff_source [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (reference : Shared.Simulator.OracleState) (before after : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (tag : FullCircuitSource) (labels : Garbling.Labels)
    (invalid : ¬ OnCurve input) (bits : labels.input = BitInput.ofAffine input)
    (mac : key.encodeAffine input = labels.inputMac)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) :
    let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
    let initial := sharedInitialSourceOracle data
    let finalState := transcriptFinalState idealOracleHandler initial before
    sample ∈ sharedCurveTagEvent rest keys table input key (sharedSourcePrefixReference reference rest) before after tag ↔
      sourceInputLabels data input = labels ∧
      SharedCurveTagGood rest keys table input sample.2 finalState (before ++ after) tag ∧
      OracleTranscriptCompatible idealOracleHandler initial before ∧
      OracleTranscriptCompatible idealOracleHandler
        (sharedProgramSelectedGateView finalState input (sample.2.encodeAffine input)
          (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
            rest.algebraic.field.curveMask.value
            (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
            input (retainedFullSource rest tag)) input)) after := by
  dsimp only
  let data : GarblingOracleData := ⟨Shared.expandOracle sample.1, sample.2, rest.encPRFOracle, rest.hashOracle⟩
  let initial := sharedInitialSourceOracle data
  let finalState := transcriptFinalState idealOracleHandler initial before
  have initialEq : {sharedSourcePrefixReference reference rest with fixedOracle := sample.1} = initial :=
    (sharedInitialSourceOracle_sample reference rest sample).symm
  have labelsEq : sourceInputLabels data input = labels ↔ sample.2.encodeAffine input = key.encodeAffine input := by
    cases labels
    dsimp only at bits mac
    simp only [sourceInputLabels, data, Garbling.Labels.mk.injEq, ← mac, ← bits, true_and]
  have histories (matching : OracleTranscriptCompatible idealOracleHandler initial before) :
      (transcriptFinalState idealOracleHandler (sharedSourcePrefixReference reference rest) before).fixedTranscript =
        finalState.fixedTranscript := by
    rw [sharedSourcePrefixReference_history reference rest before compatible]
    rw [sharedIdealTranscriptFinal_fixedHistory initial before matching]
    exact (List.append_nil _).symm
  rw [sharedInvalidSourceView_program rest keys input sample.2 tag _ invalid]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _ ∧ _ ∧ _ ∧ _
  simp only [sharedCurveTagEvent, Set.mem_setOf_eq, initialEq]
  constructor
  · rintro ⟨same, good, first, last⟩
    refine ⟨labelsEq.mpr same, ?_, first, ?_⟩
    · exact (sharedCurveTagGood_history rest keys table input sample.2 _ finalState (before ++ after) tag
        (histories first)).mp ((sharedCurveTagGood_rekey rest keys table input key sample.2 _
          (before ++ after) tag same.symm).mp good)
    · rw [sharedRetainedCurveCommands_rekey rest keys input sample.2 key tag same]
      exact last
  · rintro ⟨labelsSame, good, first, last⟩
    have same := labelsEq.mp labelsSame
    refine ⟨same, ?_, first, ?_⟩
    · exact (sharedCurveTagGood_rekey rest keys table input sample.2 key _ (before ++ after) tag same).mp
        ((sharedCurveTagGood_history rest keys table input sample.2 _ finalState (before ++ after) tag
          (histories first)).mpr good)
    · rw [← sharedRetainedCurveCommands_rekey rest keys input sample.2 key tag same]
      exact last

end
end Kriterion.ArgoMAC.Security
