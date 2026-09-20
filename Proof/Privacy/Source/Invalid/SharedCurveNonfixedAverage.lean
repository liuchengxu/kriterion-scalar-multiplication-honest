import Proof.Privacy.Source.Invalid.SharedCurveEventNonfixed
import Proof.Privacy.Source.SharedNonfixedSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveRefreshKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveRefreshKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual curve event does not read the retained nonfixed source fields. -/
theorem sharedCurveTagEvent_rest_refresh [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle) :
    sharedCurveTagEvent {rest with encPRFOracle := enc, hashOracle := hash} keys table input key initial before after tag =
      sharedCurveTagEvent rest keys table input key initial before after tag := by
  have source : retainedFullSource {rest with encPRFOracle := enc, hashOracle := hash} tag =
      retainedFullSource rest tag := rfl
  simp only [sharedCurveTagEvent, SharedCurveTagGood, sharedRetainedCurveCommands,
    retainedFullTable, SharedRetained.retainedSourceContext, SharedRetained.actualSourceContext,
    SharedRetained.contextFromSource, source]


/-- Both nonfixed functions change only the public nonfixed transcript guard. -/
theorem sharedCurveTagEvent_nonfixed_mass [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (enc : PermutationOracle EncPRF.PermutationIndex Block) (hash : EncPRF.HashOracle)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    let reference := transcriptFinalState idealOracleHandler initial before
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key {initial with encOracle := enc, hashOracle := hash} before after tag) =
    if SharedNonFixedTranscriptCompatible (initial.fixedOracle, enc, hash) (before ++ after) then
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
  by_cases other : SharedNonFixedTranscriptCompatible (initial.fixedOracle, enc, hash) (before ++ after)
  · rw [if_pos other]
    have parts := (sharedNonFixedTranscriptCompatible_append _ before after).mp other
    have first : OracleTranscriptCompatible idealOracleHandler {initial with encOracle := enc, hashOracle := hash} before := by
      rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff]
      exact ⟨((sharedPublicTranscriptCompatible_iff _ before).mp
        ((sharedIdealTranscriptCompatible_iff initial before).mp compatible)).1, parts.1⟩
    have history := (sharedIdealTranscriptFinal_fixed_fields {initial with encOracle := enc, hashOracle := hash}
      initial before rfl rfl).2
    letI : Nonempty (TranscriptOracle
        (transcriptFinalState idealOracleHandler {initial with encOracle := enc, hashOracle := hash} before).fixedTranscript) := by
      rw [history]
      infer_instance
    exact sharedCurveTagEvent_mass_at_reference rest keys table input key {initial with encOracle := enc, hashOracle := hash}
      (transcriptFinalState idealOracleHandler initial before) before after tag empty first parts.2 history
  · rw [if_neg other]
    exact sharedCurveTagEvent_zero_of_nonfixed rest keys table input key {initial with encOracle := enc, hashOracle := hash}
      before after tag other

/-- The EncPRF transcript factor equals the exact average of the actual curve event. -/
theorem sharedCurveTagEvent_encHash_average [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (encReference : PermutationTranscriptMatches initial.encOracle
      (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))))
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    encTranscriptFactor (encOracleTranscriptRecords (sharedLegacyTranscript (before ++ after))) *
      (∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
          (sharedCurveTagEvent rest keys table input key {initial with hashOracle := hash} before after tag)) =
    ∑' hash : EncPRF.HashOracle, (PMF.uniformOfFintype EncPRF.HashOracle) hash *
      ∑' enc : PermutationOracle EncPRF.PermutationIndex Block,
        (PMF.uniformOfFintype (PermutationOracle EncPRF.PermutationIndex Block)) enc *
          (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
            (sharedCurveTagEvent rest keys table input key {initial with encOracle := enc, hashOracle := hash} before after tag) := by
  simp_rw [sharedCurveTagEvent_hash_mass rest keys table input key initial _ before after tag empty compatible,
    sharedCurveTagEvent_nonfixed_mass rest keys table input key initial _ _ before after tag empty compatible]
  exact sharedNonfixedEncHash_weighted_eq {rest.reference with encPRFOracle := initial.encOracle}
    initial.fixedOracle (before ++ after) encReference _

end
end Kriterion.ArgoMAC.Security
