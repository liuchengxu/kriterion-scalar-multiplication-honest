import Proof.Privacy.Programming.SharedScheduleFreshness
import Proof.Privacy.Source.SharedCurveMass
import Proof.Privacy.Collision.CurveScheduleDomains

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local irreducible] pipelineGateSchedule scheduleCommands Shared.Simulator.commandRecords

private theorem sharedCurveIndex_iff (index : Pipeline.FixedKeyIndex) :
    isCurveIndex index ↔ sharedCurveSlot (Shared.fixedIndex index) = true := by
  cases index with
  | mk kind position slot => cases kind <;> simp [isCurveIndex, sharedCurveSlot, Shared.fixedIndex]

/-- The curve-only command list contains exactly the curve records of the full command list. -/
theorem sharedCurveRecords_filter
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveMac pointMac : InputMac) (record : PermutationRecord Shared.FixedKeyIndex Block) :
    record ∈ Shared.Simulator.commandRecords (scheduleCommands (curve.schedule input curveMac)) ↔
      record ∈ Shared.Simulator.commandRecords (scheduleCommands
        (pipelineGateSchedule curve points input curveMac pointMac)) ∧ sharedCurveSlot record.index = true := by
  rw [sharedScheduleRecords_eq, sharedScheduleRecords_eq]
  constructor
  · rintro member
    obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp member
    have filtered := (curveGateProgramRecords_filter curve points input curveMac pointMac prior).mp priorMember
    exact ⟨List.mem_map.mpr ⟨prior, filtered.1, rfl⟩, (sharedCurveIndex_iff _).mp filtered.2⟩
  · rintro ⟨member, curveIndex⟩
    obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨prior,
      (curveGateProgramRecords_filter curve points input curveMac pointMac prior).mpr
        ⟨priorMember, (sharedCurveIndex_iff _).mpr curveIndex⟩, rfl⟩

/-- The invalid-input schedule covers only the selected curve domains. -/
theorem sharedCurveRecords_domains
    (bridgeKey mask : BaseField) (rows : FieldMacToECMac.Rows) (input : AffineInput)
    (source : CircuitMaskSample) (curveKey pointKey : InputMacKey) (index : Shared.FixedKeyIndex) :
    let sample := circuitMaskSampleGarble bridgeKey mask rows input source
    let gates := sourceGatePrescription source pointKey curveKey
      (fun gate => goodHashLiftSource ((circuitMaskHashSplitEquiv source).1 gate))
    SharedQueryCounts.programmedDomains (Shared.Simulator.commandRecords (scheduleCommands
      (sample.curveRequest.schedule input (curveKey.encodeAffine input)))) index =
      sharedCurveDomains gates (sharedCircuitSelected input) index := by
  dsimp only
  unfold sharedCurveDomains
  rw [← sharedCircuitRecords_domains bridgeKey mask rows input source curveKey pointKey index]
  ext domain
  simp only [SharedQueryCounts.programmedDomains, Set.mem_setOf_eq,
    sharedCurveRecords_filter _ (circuitMaskSampleGarble bridgeKey mask rows input source).pointRequests input (curveKey.encodeAffine input) (pointKey.encodeAffine input)]
  by_cases curve : sharedCurveSlot index = true
  · rw [if_pos curve]
    constructor
    · rintro ⟨record, ⟨member, _⟩, indexed, same⟩
      exact ⟨record, member, indexed, same⟩
    · rintro ⟨record, member, indexed, same⟩
      exact ⟨record, ⟨member, indexed ▸ curve⟩, indexed, same⟩
  · rw [if_neg curve]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨record, ⟨_, member⟩, indexed, _⟩
    exact curve (indexed ▸ member)

end
end Kriterion.ArgoMAC.Security
