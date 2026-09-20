import Proof.Privacy.Source.Valid.SharedPipelineGlobalRatio
import Proof.Privacy.Transcript.SharedIdealGateGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- A valid input links the shared schedule with the retained bridge key. -/
theorem sharedCircuitMaskSampleGarble_linkedSchedule (state : Shared.Simulator.OracleState)
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (source : CircuitMaskSample) (key : InputMacKey) (valid : OnCurve input) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    linkedPipelineGateSchedule state sample.curveRequest sample.pointRequests input (key.encodeAffine input) =
      pipelineGateSchedule sample.curveRequest sample.pointRequests input (key.encodeAffine input)
        ((EncPRF.transformKey state.encOracle (EncPRF.whiteningKeys state.hashOracle bridgeKey) key).encodeAffine input) := by
  dsimp only
  have result := circuitMaskSampleGarble_curveResult bridgeKey mask rows input source
  have residual : input.x ^ 3 + 3 - input.y ^ 2 = 0 := sub_eq_zero.mpr valid.symm
  rw [residual, mul_zero, add_zero] at result
  simp only [linkedPipelineGateSchedule, linkedPointInputMac, result, InputMacKey.encodeAffine,
    EncPRF.transformEncode]

/-- The valid selected view executes the exact retained pipeline commands. -/
theorem sharedValidSourceView_program [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (key : InputMacKey) (tag : FullCircuitSource)
    (state : Shared.Simulator.OracleState) (valid : OnCurve input)
    (enc : state.encOracle = rest.encPRFOracle) (hash : state.hashOracle = rest.hashOracle) :
    sharedProgramSelectedGateView state input (key.encodeAffine input)
      (selectedGateView (circuitMaskSampleGarble rest.algebraic.field.bridgeKey
        rest.algebraic.field.curveMask.value
        (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
        input (retainedFullSource rest tag)) input) =
      Shared.Simulator.commands state (sharedRetainedPipelineCommands rest keys input key tag) := by
  obtain ⟨point, decoded⟩ := Option.ne_none_iff_exists'.mp ((decodePoint_defined input).mpr valid)
  simp only [selectedGateView, decoded, Option.map_some, sharedProgramSelectedGateView]
  rw [sharedCircuitMaskSampleGarble_linkedSchedule state rest.algebraic.field.bridgeKey
    rest.algebraic.field.curveMask.value
    (FieldMacToECMac.rowsForOutputKeys keys rest.algebraic.point.pointRandomness)
    input (retainedFullSource rest tag) key valid]
  simp only [enc, hash, Shared.Simulator.program, sharedRetainedPipelineCommands]

/-- The selected MAC fixes every retained pipeline command. -/
theorem sharedRetainedPipelineCommands_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (input : AffineInput) (first second : InputMacKey) (tag : FullCircuitSource)
    (same : first.encodeAffine input = second.encodeAffine input) :
    sharedRetainedPipelineCommands rest keys input first tag =
      sharedRetainedPipelineCommands rest keys input second tag := by
  have linked : (EncPRF.transformKey rest.encPRFOracle
      (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) first).encodeAffine input =
      (EncPRF.transformKey rest.encPRFOracle
        (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) second).encodeAffine input := by
    simpa only [InputMacKey.encodeAffine, EncPRF.transformEncode] using
      congrArg (EncPRF.transformMac rest.encPRFOracle
        (EncPRF.whiteningKeys rest.hashOracle rest.algebraic.field.bridgeKey) (BitInput.ofAffine input)) same
  simp only [sharedRetainedPipelineCommands, same, linked]

/-- The selected MAC fixes the complete pipeline guard. -/
theorem sharedPipelineTagGood_rekey [FieldCertificate] [GroupCertificate]
    (rest : GarblingSourceRest) (keys : FieldMacToECMac.OutputKeys)
    (table : Pipeline.Table) (input : AffineInput) (first second : InputMacKey)
    (state : Shared.Simulator.OracleState) (tag : FullCircuitSource)
    (same : first.encodeAffine input = second.encodeAffine input) :
    SharedPipelineTagGood rest keys table input first state tag ↔
      SharedPipelineTagGood rest keys table input second state tag := by
  unfold SharedPipelineTagGood
  dsimp only
  rw [sharedRetainedPipelineCommands_rekey rest keys input first second tag same]
  rfl

end
end Kriterion.ArgoMAC.Security
