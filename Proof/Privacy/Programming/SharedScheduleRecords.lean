import Proof.Privacy.Source.SharedActiveMass
import Proof.Privacy.Distribution.SharedProgrammingDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 2048

/-- This record uses the paper slot and keeps the requested permutation pair. -/
def sharedProgramRecord (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    PermutationRecord Shared.FixedKeyIndex Block :=
  ⟨.program, .simulator, Shared.fixedIndex record.index, record.domain, record.range⟩

/-- The actual shared command list contains exactly the selected directive records. -/
theorem mem_sharedScheduleRecords_iff (schedule : List GateDirective)
    (record : PermutationRecord Shared.FixedKeyIndex Block) :
    record ∈ Shared.Simulator.commandRecords (scheduleCommands schedule) ↔
      ∃ directive ∈ schedule, ∃ slot, rawSlotBranch slot = directive.bit ∧
        sharedProgramRecord (directive.slotRecord slot) = record := by
  simp only [Shared.Simulator.commandRecords, scheduleCommands, List.mem_map, List.mem_flatMap,
    GateDirective.commands, List.mem_reverse]
  constructor
  · rintro ⟨command, ⟨directive, member, prior, priorMember, rfl⟩, equal⟩
    obtain ⟨slot, active, rfl⟩ := (GateDirective.mem_programRecords_iff directive prior).mp priorMember
    exact ⟨directive, member, slot, active, equal⟩
  · rintro ⟨directive, member, slot, active, equal⟩
    exact ⟨_, ⟨directive, member, _, (GateDirective.mem_programRecords_iff directive _).mpr
      ⟨slot, active, rfl⟩, rfl⟩, equal⟩

/-- Each actual circuit bucket selects one input bit in all three shared slots. -/
def sharedCircuitSelected (input : AffineInput) (index : Shared.FixedKeyIndex) : Bool :=
  circuitBucketInputBit input (index.kind, index.position)

/-- The actual shared circuit schedule contains exactly its selected raw records. -/
theorem mem_sharedCircuitRecords_iff
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey)
    (record : PermutationRecord Shared.FixedKeyIndex Block) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let gates := sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    record ∈ Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input))) ↔
      ∃ index, ∃ use : SharedActiveUse gates index (sharedCircuitSelected input index),
        sharedProgramRecord ((gates use.1.1.1).slotRecord use.1.1.2) = record := by
  dsimp only
  rw [mem_sharedScheduleRecords_iff]
  constructor
  · rintro ⟨directive, member, slot, active, equal⟩
    obtain ⟨gate, rfl⟩ := (mem_pipelineGateSchedule_iff _ _ _ _ _ directive).mp member
    refine ⟨Shared.fixedIndex (fixedKeyIndex (rawCircuitLocation gate) (rawCircuitWindow gate) slot),
      ⟨⟨(gate, slot), rfl⟩, ?_⟩, ?_⟩
    · exact active.trans (actualCircuitDirective_bit _ _ _ _ _ gate slot)
    · rw [← circuitMaskDirective_record_eq_raw bridgeKey mask rows input source curveKey pointKey gate slot active]
      exact equal
  · rintro ⟨index, ⟨⟨⟨gate, slot⟩, sameIndex⟩, selected⟩, equal⟩
    have active : rawSlotBranch slot = (actualCircuitDirective
        (circuitMaskSampleGarble bridgeKey mask rows input source).curveRequest
        (circuitMaskSampleGarble bridgeKey mask rows input source).pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input) gate).bit := by
      rw [actualCircuitDirective_bit _ _ _ _ _ gate slot]
      change rawSlotBranch slot = sharedCircuitSelected input index at selected
      rw [← sameIndex] at selected
      exact selected
    refine ⟨_, (mem_pipelineGateSchedule_iff _ _ _ _ _ _).mpr ⟨gate, rfl⟩, slot, active, ?_⟩
    rw [circuitMaskDirective_record_eq_raw bridgeKey mask rows input source curveKey pointKey gate slot active]
    exact equal

/-- The actual shared schedule has exactly the selected source domains. -/
theorem sharedCircuitRecords_domains
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey) (index : Shared.FixedKeyIndex) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let gates := sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule sample.curveRequest sample.pointRequests input
        (curveKey.encodeAffine input) (pointKey.encodeAffine input)))) index =
      sharedActiveDomains gates (sharedCircuitSelected input) index := by
  dsimp only
  ext domain
  constructor
  · rintro ⟨record, member, indexed, sameDomain⟩
    obtain ⟨bucket, use, rfl⟩ := (mem_sharedCircuitRecords_iff
      bridgeKey mask rows input source curveKey pointKey record).mp member
    have sameBucket : bucket = index := use.1.2.symm.trans indexed
    subst bucket
    exact ⟨use, sameDomain⟩
  · rintro ⟨use, sameDomain⟩
    refine ⟨_, (mem_sharedCircuitRecords_iff bridgeKey mask rows input source curveKey pointKey _).mpr
      ⟨index, use, rfl⟩, use.1.2, sameDomain⟩

end
end Kriterion.ArgoMAC.Security
