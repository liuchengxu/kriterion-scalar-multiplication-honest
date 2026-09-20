import Proof.Privacy.Programming.SharedScheduleCompatibility
import Proof.Privacy.Collision.ActualScheduleFreshness

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The actual shared interpreter maps the selected raw record list in the same order. -/
theorem sharedScheduleRecords_eq (schedule : List GateDirective) :
    Shared.Simulator.commandRecords (scheduleCommands schedule) =
      (gateProgramRecords schedule).map sharedProgramRecord := by
  simp only [Shared.Simulator.commandRecords, scheduleCommands, GateDirective.commands,
    gateProgramRecords, List.map_flatMap, List.map_map]
  rfl

/-- A shared index and its branch identify the original role index. -/
theorem sharedIndex_branch_injective : Function.Injective
    (fun index : Pipeline.FixedKeyIndex => (Shared.fixedIndex index, rawSlotBranch index.slot)) := by
  intro first second equal
  have shared := congrArg Prod.fst equal
  have branches := congrArg Prod.snd equal
  have slots := sharedRole_injective (Prod.ext (congrArg Shared.FixedKeyIndex.slot shared) branches)
  cases first
  cases second
  congr
  · exact congrArg Shared.FixedKeyIndex.kind shared
  · exact congrArg Shared.FixedKeyIndex.position shared

private theorem sharedRecords_pairwise
    (records : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (selected : Shared.FixedKeyIndex → Bool)
    (active : ∀ record ∈ records, rawSlotBranch record.index.slot = selected (Shared.fixedIndex record.index))
    (distinct : records.Pairwise fun first second => first.index = second.index →
      first.domain ≠ second.domain ∧ first.range ≠ second.range) :
    (records.map sharedProgramRecord).Pairwise fun first second => first.index = second.index →
      first.domain ≠ second.domain ∧ first.range ≠ second.range := by
  induction records with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      rw [List.map_cons, List.pairwise_cons]
      have pairwise := List.pairwise_cons.mp distinct
      constructor
      · intro second member same
        obtain ⟨second, priorMember, rfl⟩ := List.mem_map.mp member
        have branches := (active first (List.mem_cons_self ..)).trans
          ((congrArg selected same).trans (active second (List.mem_cons_of_mem _ priorMember)).symm)
        exact pairwise.1 second priorMember (sharedIndex_branch_injective (Prod.ext same branches))
      · exact ih (fun record member => active record (List.mem_cons_of_mem _ member)) pairwise.2

/-- The actual shared schedule preserves within-branch record separation. -/
theorem sharedPipelineGateRecords_pairwise
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (distinct : (gateProgramRecords (pipelineGateSchedule curve points input curveInputMac pointInputMac)).Pairwise
      fun first second => first.index = second.index → first.domain ≠ second.domain ∧ first.range ≠ second.range) :
    (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule curve points input curveInputMac pointInputMac))).Pairwise
      fun first second => first.index = second.index → first.domain ≠ second.domain ∧ first.range ≠ second.range := by
  rw [sharedScheduleRecords_eq]
  apply sharedRecords_pairwise _ (sharedCircuitSelected input) _ distinct
  intro record member
  obtain ⟨gate, slot, active, rfl⟩ :=
    (mem_pipelineGateProgramRecords_iff curve points input curveInputMac pointInputMac record).mp member
  rw [actualCircuitDirective_slotRecord_index]
  exact active.trans (actualCircuitDirective_bit curve points input curveInputMac pointInputMac gate slot)

/-- A shared prequery check and the actual row separation make the complete schedule fresh. -/
theorem sharedPipelineGateRecords_fresh
    (history : List (PermutationRecord Shared.FixedKeyIndex Block))
    (curve : CurveGateRequest) (points : PointGateRequests) (input : AffineInput)
    (curveInputMac pointInputMac : InputMac)
    (distinct : (gateProgramRecords (pipelineGateSchedule curve points input curveInputMac pointInputMac)).Pairwise
      fun first second => first.index = second.index → first.domain ≠ second.domain ∧ first.range ≠ second.range)
    (prior : ∀ directive ∈ pipelineGateSchedule curve points input curveInputMac pointInputMac,
      ∀ slot, rawSlotBranch slot = directive.bit →
      let record := sharedProgramRecord (directive.slotRecord slot)
      FreshPermutationPair history record.index record.domain record.range) :
    FreshRecordSchedule history (Shared.Simulator.commandRecords (scheduleCommands
      (pipelineGateSchedule curve points input curveInputMac pointInputMac))) := by
  apply freshRecordSchedule_of_pairwise
  · intro record member
    obtain ⟨directive, directiveMember, slot, active, rfl⟩ := (mem_sharedScheduleRecords_iff _ record).mp member
    exact prior directive directiveMember slot active
  · exact sharedPipelineGateRecords_pairwise curve points input curveInputMac pointInputMac distinct

end
end Kriterion.ArgoMAC.Security
