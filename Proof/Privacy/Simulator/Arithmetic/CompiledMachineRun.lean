import Proof.Privacy.Simulator.Arithmetic.CompiledMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The setup body retains its exact source law and pays two dispatch instructions. -/
theorem compiledMachine_setupRun [BN254.FieldCertificate] (attempts fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: false :: body) :
    run (compiledMachine attempts) (2 + fuel) ⟨0, memory⟩ =
      (run (offlineMachine attempts) fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseSetupLabels (offlineMachine attempts) (onlineMachine attempts)
            (recordedPublicHandler attempts)) result.1, result.2 + 2)) :=
  phaseMachine_setupRun _ _ _ (compiledMachine_fits attempts) fuel memory body wire

/-- The online body retains its exact source law and pays two dispatch instructions. -/
theorem compiledMachine_onlineRun [BN254.FieldCertificate] (attempts fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: true :: body) :
    run (compiledMachine attempts) (2 + fuel) ⟨0, memory⟩ =
      (run (onlineMachine attempts) fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseOnlineLabels (offlineMachine attempts) (onlineMachine attempts)
            (recordedPublicHandler attempts)) result.1, result.2 + 2)) :=
  phaseMachine_onlineRun _ _ _ (compiledMachine_fits attempts) fuel memory body wire

/-- The public query retains its exact source law and pays two dispatch instructions. -/
theorem compiledMachine_queryRun [BN254.FieldCertificate] (attempts fuel : Nat)
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = true :: false :: body) :
    run (compiledMachine attempts) (2 + fuel) ⟨0, memory⟩ =
      (run (recordedPublicHandler attempts) fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseQueryLabels (offlineMachine attempts) (onlineMachine attempts)
            (recordedPublicHandler attempts)) result.1, result.2 + 2)) :=
  phaseMachine_queryRun _ _ _ (compiledMachine_fits attempts) fuel memory body wire

end Kriterion.ArgoMAC.ArithmeticSimulator
