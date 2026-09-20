import Proof.Privacy.Source.Invalid.SharedCurveGlobalRatio
import Proof.Privacy.Transcript.SharedIdealGateGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- An invalid selected view executes exactly the retained shared curve commands. -/
theorem sharedInvalidSourceView_program [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : Shared.Simulator.OracleState) (invalid : ¬ OnCurve input) :
    sharedProgramSelectedGateView state input (key.encodeAffine input)
      (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input) =
      Shared.Simulator.commands state (sharedRetainedCurveCommands rest keys input key tag) := by
  have decoded : decodePoint input = none :=
    Classical.not_not.mp (fun nonzero => invalid ((decodePoint_defined input).mp nonzero))
  simp only [selectedGateView, decoded, Option.map_none, sharedProgramSelectedGateView,
    Shared.Simulator.program, sharedRetainedCurveCommands]

/-- The selected MAC fixes every retained shared curve command. -/
theorem sharedRetainedCurveCommands_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (first second : InputMacKey) (tag : FullCircuitSource)
    (same : first.encodeAffine input = second.encodeAffine input) :
    sharedRetainedCurveCommands rest keys input first tag =
      sharedRetainedCurveCommands rest keys input second tag := by
  simp only [sharedRetainedCurveCommands, same]

/-- The selected MAC fixes every shared curve source guard. -/
theorem sharedCurveTagGood_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (first second : InputMacKey)
    (state : Shared.Simulator.OracleState) (transcript : List (Sigma sharedRealOracleSpec.Answer))
    (tag : FullCircuitSource) (same : first.encodeAffine input = second.encodeAffine input) :
    SharedCurveTagGood rest keys table input first state transcript tag ↔
      SharedCurveTagGood rest keys table input second state transcript tag := by
  unfold SharedCurveTagGood
  dsimp only
  rw [sharedRetainedCurveCommands_rekey rest keys input first second tag same]
  rfl

end
end Kriterion.ArgoMAC.Security
