import Proof.Privacy.Programming.SharedScheduleRecords

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048
attribute [local instance] instFintypeRawCircuitGate_1

/-- Injective actual source records give the exact active domain count in the shared schedule. -/
theorem sharedCircuitRecords_domainCount [Fintype Block]
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey) (index : Shared.FixedKeyIndex)
    (injective : Function.Injective (sharedRawBucketDomain
      (sourceGatePrescription source pointKey curveKey
        (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))) index)) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input)))) index) =
      (if index.slot.val < 2 ∨ sharedCircuitSelected input index = false then 1 else 0) *
        circuitBucketSize ⟨index.kind, index.position, .hash 0⟩ := by
  dsimp only
  let gates := sourceGatePrescription source pointKey curveKey
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
  let domain := fun use : SharedActiveUse gates index (sharedCircuitSelected input index) =>
    sharedRawBucketDomain gates index use.1
  have domainInjective : Function.Injective domain := injective.comp Subtype.val_injective
  have sets := sharedCircuitRecords_domains bridgeKey mask rows input source curveKey pointKey index
  have count : Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule (circuitMaskSampleGarble bridgeKey mask rows input source).curveRequest
        (circuitMaskSampleGarble bridgeKey mask rows input source).pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input)))) index) =
      Fintype.card (SharedActiveUse gates index (sharedCircuitSelected input index)) := by
    exact Fintype.card_congr ((Equiv.setCongr sets).trans (Equiv.ofInjective domain domainInjective).symm)
  rw [count]
  have card := sharedActiveUse_card (circuitGateKey pointKey curveKey) (circuitSourceSlope source)
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    (circuitSourceTable source) index (sharedCircuitSelected input index)
  convert card using 1
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)

end
end Kriterion.ArgoMAC.Security
