import Proof.Privacy.Programming.SharedCurveRecords
import Proof.Privacy.Programming.SharedScheduleBound

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords

/-- The actual curve-only schedule fixes every selected curve source record. -/
theorem sharedCurveSourceSchedule_active
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (reference : PermutationOracle Shared.FixedKeyIndex Block)
    (compatible :
      let sample := circuitMaskSampleGarble bridgeKey mask rows input source
      PermutationTranscriptMatches reference (Shared.Simulator.commandRecords (scheduleCommands
        (sample.curveRequest.schedule input (curveKey.encodeAffine input)))))
    (gate : RawCircuitGate) (slot : Pipeline.FixedKeySlot)
    (curve : sharedCurveSlot (Shared.fixedIndex
      (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot)) = true)
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
  exact compatible _ ((sharedCurveRecords_filter _ _ input (curveKey.encodeAffine input)
    (pointKey.encodeAffine input) _).mpr ⟨member, curve⟩)

/-- The actual curve-only command count fits every complete shared source bucket. -/
theorem sharedCurveRecords_domainCount_le [Fintype Block]
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey) (index : Shared.FixedKeyIndex) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    Fintype.card (SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
      (sample.curveRequest.schedule input (curveKey.encodeAffine input)))) index) ≤ sharedCircuitBucketSize index := by
  classical
  dsimp only
  let sample := circuitMaskSampleGarble bridgeKey mask rows input source
  let embed : SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
      (sample.curveRequest.schedule input (curveKey.encodeAffine input)))) index →
      SharedQueryDomain (Shared.Simulator.commandRecords (scheduleCommands
        (pipelineGateSchedule sample.curveRequest sample.pointRequests input
          (curveKey.encodeAffine input) (pointKey.encodeAffine input)))) index := fun query =>
    ⟨query.1, by
      obtain ⟨record, member, indexed, equal⟩ := query.2
      exact ⟨record, ((sharedCurveRecords_filter _ _ input (curveKey.encodeAffine input)
        (pointKey.encodeAffine input) record).mp member).1, indexed, equal⟩⟩
  have injective : Function.Injective embed := by
    intro first second equal
    have same := congrArg Subtype.val equal
    exact Subtype.ext same
  exact (Fintype.card_le_of_injective embed injective).trans
    (sharedCircuitRecords_domainCount_le bridgeKey mask rows input source curveKey pointKey index)

end
end Kriterion.ArgoMAC.Security
