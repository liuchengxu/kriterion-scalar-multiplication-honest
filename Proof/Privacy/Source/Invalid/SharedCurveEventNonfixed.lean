import Proof.Privacy.Source.Invalid.SharedCurveEventReference

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveNonfixedKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveNonfixedKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Every retained curve event satisfies both nonfixed transcript phases. -/
theorem sharedCurveTagEvent_nonfixed [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (sample : (PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)
    (member : sample ∈ sharedCurveTagEvent rest keys table input key initial before after tag) :
    SharedNonFixedTranscriptCompatible (initial.fixedOracle, initial.encOracle, initial.hashOracle)
      (before ++ after) := by
  have first := (sharedPublicTranscriptCompatible_iff _ before).mp
    ((sharedIdealTranscriptCompatible_iff _ before).mp member.2.2.1)
  have second := (sharedPublicTranscriptCompatible_iff _ after).mp
    ((sharedIdealTranscriptCompatible_iff _ after).mp member.2.2.2)
  have others := Shared.Simulator.commands_other
    (transcriptFinalState idealOracleHandler {initial with fixedOracle := sample.1} before)
    (sharedRetainedCurveCommands rest keys input key tag)
  have final := sharedIdealTranscriptFinal_oracles {initial with fixedOracle := sample.1} before
  rw [others.1, others.2, final.2.1, final.2.2] at second
  exact (sharedNonFixedTranscriptCompatible_append _ before after).mpr
    ⟨(sharedNonFixedTranscriptCompatible_fixed _ initial.fixedOracle _ _ before).mp first.2,
      (sharedNonFixedTranscriptCompatible_fixed _ initial.fixedOracle _ _ after).mp second.2⟩

/-- An incompatible nonfixed transcript has zero retained curve-event mass. -/
theorem sharedCurveTagEvent_zero_of_nonfixed [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (nonfixed : ¬ SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, initial.hashOracle) (before ++ after)) :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key initial before after tag) = 0 := by
  have empty : sharedCurveTagEvent rest keys table input key initial before after tag = ∅ := by
    ext sample
    exact iff_false_intro fun member => nonfixed
      (sharedCurveTagEvent_nonfixed rest keys table input key initial before after tag sample member)
  rw [empty]
  simp

/-- A changed hash oracle preserves the exact curve mass when its public answers match. -/
theorem sharedCurveTagEvent_hash_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState) (hash : EncPRF.HashOracle)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    let reference := transcriptFinalState idealOracleHandler initial before
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key {initial with hashOracle := hash} before after tag) =
    if SharedNonFixedTranscriptCompatible (initial.fixedOracle, initial.encOracle, hash) (before ++ after) then
      if SharedCurveTagGood rest keys table input key reference (before ++ after) tag then
        (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
          (Shared.Simulator.transcriptMass reference.fixedTranscript *
            ((PMF.uniformOfFintype (TranscriptOracle reference.fixedTranscript)).map
                (fun oracle => Shared.Simulator.commands {reference with fixedOracle := oracle.1}
                  (sharedRetainedCurveCommands rest keys input key tag))).toOuterMeasure
                    {programmed | PermutationTranscriptMatches programmed.fixedOracle (sharedFixedTranscriptRecords after)})
      else 0
    else 0 := by
  dsimp only
  by_cases other : SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, hash) (before ++ after)
  · rw [if_pos other]
    have parts := (sharedNonFixedTranscriptCompatible_append _ before after).mp other
    have first : OracleTranscriptCompatible idealOracleHandler {initial with hashOracle := hash} before := by
      rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff]
      exact ⟨((sharedPublicTranscriptCompatible_iff _ before).mp
        ((sharedIdealTranscriptCompatible_iff initial before).mp compatible)).1, parts.1⟩
    have history := (sharedIdealTranscriptFinal_fixed_fields {initial with hashOracle := hash}
      initial before rfl rfl).2
    letI : Nonempty (TranscriptOracle
        (transcriptFinalState idealOracleHandler {initial with hashOracle := hash} before).fixedTranscript) := by
      rw [history]
      infer_instance
    exact sharedCurveTagEvent_mass_at_reference rest keys table input key {initial with hashOracle := hash}
      (transcriptFinalState idealOracleHandler initial before) before after tag empty first parts.2 history
  · rw [if_neg other]
    exact sharedCurveTagEvent_zero_of_nonfixed rest keys table input key {initial with hashOracle := hash}
      before after tag other

end
end Kriterion.ArgoMAC.Security
