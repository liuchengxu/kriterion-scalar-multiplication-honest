import Proof.Privacy.Source.Invalid.SharedCurveEventMass
import Proof.Privacy.Simulator.SharedFixedStateCongr

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
attribute [local instance] transcriptOracleFintype bitAdaptorTableFintype
  instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
local instance curveReferenceKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance curveReferenceKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The curve source guard reads only the recorded fixed history of the reference state. -/
theorem sharedCurveTagGood_history [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (first second : Shared.Simulator.OracleState) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource) (history : first.fixedTranscript = second.fixedTranscript) :
    SharedCurveTagGood rest keys table input key first transcript tag ↔
      SharedCurveTagGood rest keys table input key second transcript tag := by
  simp only [SharedCurveTagGood, history]

/-- A shared source event can use any reference state with the same fixed history. -/
theorem sharedCurveTagEvent_mass_at_reference [FieldCertificate] [GroupCertificate] [Fintype Block]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (key : InputMacKey)
    (initial reference : Shared.Simulator.OracleState)
    (before after : List (Sigma sharedRealOracleSpec.Answer)) (tag : FullCircuitSource)
    (empty : initial.fixedTranscript = [])
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    (nonfixed : SharedNonFixedTranscriptCompatible
      (initial.fixedOracle, initial.encOracle, initial.hashOracle) after)
    (history : (transcriptFinalState idealOracleHandler initial before).fixedTranscript = reference.fixedTranscript)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)]
    [Nonempty (TranscriptOracle reference.fixedTranscript)] :
    (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      (sharedCurveTagEvent rest keys table input key initial before after tag) =
    if SharedCurveTagGood rest keys table input key reference (before ++ after) tag then
      (Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ *
        (Shared.Simulator.transcriptMass reference.fixedTranscript *
          ((PMF.uniformOfFintype (TranscriptOracle reference.fixedTranscript)).map
              (fun oracle => Shared.Simulator.commands {reference with fixedOracle := oracle.1}
                (sharedRetainedCurveCommands rest keys input key tag))).toOuterMeasure
                  {programmed | PermutationTranscriptMatches programmed.fixedOracle (sharedFixedTranscriptRecords after)})
    else 0 := by
  rw [sharedCurveTagEvent_mass rest keys table input key initial before after tag empty compatible nonfixed,
    sharedCurveTagGood_history rest keys table input key _ reference (before ++ after) tag history]
  by_cases good : SharedCurveTagGood rest keys table input key reference (before ++ after) tag
  · rw [if_pos good, if_pos good]
    apply congrArg ((Fintype.card (EncPRF.PermutationIndex → Block) : ENNReal)⁻¹ * ·)
    exact congrArg₂ (· * ·) (congrArg Shared.Simulator.transcriptMass history)
      (sharedCommands_conditional_mass_congr _ reference (sharedRetainedCurveCommands rest keys input key tag)
        (sharedFixedTranscriptRecords after) history)
  · rw [if_neg good, if_neg good]

end
end Kriterion.ArgoMAC.Security
