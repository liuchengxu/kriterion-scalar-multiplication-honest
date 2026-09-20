import Proof.Privacy.Simulator.Arithmetic.PhaseMachineCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The setup request adds exactly two dispatch instructions to its body run. -/
theorem phaseMachine_setupRun [BN254.FieldCertificate] (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) (fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: false :: body) :
    run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ =
      (run setup fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseSetupLabels setup online query) result.1, result.2 + 2)) := by
  have dispatch := phaseDispatch_continue (phaseMachine setup online query fits)
    (phaseMachineLabels setup online query) (phaseMachine_dispatch setup online query fits)
    memory false false body wire fuel
  change run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ = _ at dispatch
  rw [dispatch]
  change (run (phaseMachine setup online query fits) fuel
    (relocateConfiguration (phaseSetupLabels setup online query) ⟨0, phaseDispatchMemory memory body⟩)).map _ = _
  rw [relocate_run (phaseMachine setup online query fits) setup (phaseSetupLabels setup online query)
      (phaseMachine_setup setup online query fits) fuel ⟨0, phaseDispatchMemory memory body⟩,
    PMF.map_comp]
  simp [Function.comp_def, Option.map_map]
  rfl

/-- The online request adds exactly two dispatch instructions to its body run. -/
theorem phaseMachine_onlineRun [BN254.FieldCertificate] (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) (fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: true :: body) :
    run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ =
      (run online fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseOnlineLabels setup online query) result.1, result.2 + 2)) := by
  have dispatch := phaseDispatch_continue (phaseMachine setup online query fits)
    (phaseMachineLabels setup online query) (phaseMachine_dispatch setup online query fits)
    memory false true body wire fuel
  change run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ = _ at dispatch
  rw [dispatch]
  change (run (phaseMachine setup online query fits) fuel
    (relocateConfiguration (phaseOnlineLabels setup online query) ⟨0, phaseDispatchMemory memory body⟩)).map _ = _
  rw [relocate_run (phaseMachine setup online query fits) online (phaseOnlineLabels setup online query)
      (phaseMachine_online setup online query fits) fuel ⟨0, phaseDispatchMemory memory body⟩,
    PMF.map_comp]
  simp [Function.comp_def, Option.map_map]
  rfl

/-- The query request adds exactly two dispatch instructions to its body run. -/
theorem phaseMachine_queryRun [BN254.FieldCertificate] (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) (fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = true :: false :: body) :
    run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ =
      (run query fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseQueryLabels setup online query) result.1, result.2 + 2)) := by
  have dispatch := phaseDispatch_continue (phaseMachine setup online query fits)
    (phaseMachineLabels setup online query) (phaseMachine_dispatch setup online query fits)
    memory true false body wire fuel
  change run (phaseMachine setup online query fits) (2 + fuel) ⟨0, memory⟩ = _ at dispatch
  rw [dispatch]
  change (run (phaseMachine setup online query fits) fuel
    (relocateConfiguration (phaseQueryLabels setup online query) ⟨0, phaseDispatchMemory memory body⟩)).map _ = _
  rw [relocate_run (phaseMachine setup online query fits) query (phaseQueryLabels setup online query)
      (phaseMachine_query setup online query fits) fuel ⟨0, phaseDispatchMemory memory body⟩,
    PMF.map_comp]
  simp [Function.comp_def, Option.map_map]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
