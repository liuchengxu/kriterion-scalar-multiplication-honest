import Proof.Privacy.Source.SharedRetainedPostquery

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- The actual shared schedule fixes every selected source record in its reference oracle. -/
theorem sharedSourceSchedule_active
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (compatible :
      let sample := circuitMaskSampleGarble bridgeKey mask rows input source
      PermutationTranscriptMatches reference (Shared.Simulator.commandRecords (scheduleCommands
        (pipelineGateSchedule sample.curveRequest sample.pointRequests input
          (curveKey.encodeAffine input) (pointKey.encodeAffine input)))))
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (active : rawSlotBranch slot = inputSelectedLabelBit input (circuitGateWire gate)) :
    let gates := sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    let record := (gates gate).slotRecord slot
    reference.permutation (Shared.fixedIndex record.index) record.domain = record.range := by
  let gates := sourceGatePrescription source pointKey curveKey
    (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
  let index := Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)
  have selected : rawSlotBranch slot = sharedCircuitSelected input index :=
    active.trans (sharedCircuitSelected_wire input gate slot).symm
  let use : SharedActiveUse gates index (sharedCircuitSelected input index) := ⟨⟨(gate, slot), rfl⟩, selected⟩
  have member := (mem_sharedCircuitRecords_iff bridgeKey mask rows input source curveKey pointKey
    (sharedProgramRecord ((gates gate).slotRecord slot))).mpr ⟨index, use, rfl⟩
  exact compatible _ member

end
end Kriterion.ArgoMAC.Security
