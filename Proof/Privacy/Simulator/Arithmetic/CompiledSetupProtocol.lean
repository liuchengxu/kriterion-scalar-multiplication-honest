import Proof.Privacy.Simulator.Arithmetic.CompiledMachineRun
import Proof.Privacy.Simulator.Arithmetic.OfflineMachineProtocol
import Proof.Privacy.Simulator.Arithmetic.RespondSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan samplerBatchMemory
  Wire.encoding publicValue

private theorem setupBudget (machine : Machine) (fuel : Nat)
    (table : machine.size + 1 ≤ 600000000) (execution : fuel ≤ 605084290688) :
    (initial machine).spent + (2 + fuel) ≤ budget 0 := by
  change machine.size + 1 + (2 + fuel) ≤ budget 0
  rw [budget_expanded]
  omega

private theorem executionBudget (size fuel : Nat)
    (total : size + 1 + fuel ≤ 605084290688) : fuel ≤ 605084290688 := by omega

/-- The setup request pays for the complete control table and both dispatch instructions. -/
theorem compiledMachine_setupBudget :
    (initial (compiledMachine 256)).spent +
      (2 + (batchStepBudget 256 * 838208 + publicWireProgram.length + 3)) ≤ budget 0 :=
  setupBudget (compiledMachine 256) _ (compiledMachine_tableCost 256)
    (executionBudget (offlineMachine 256).size _ offlineMachine_budget)

/-- The setup response retains the sampled memory and the exact instruction charge. -/
theorem compiledMachine_setupResponse [FieldCertificate] (attempts parameter : Nat)
    (attemptFits : attempts < 2 ^ 256)
    (enough : (initial (compiledMachine attempts)).spent +
      (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)) ≤ budget 0) :
    respond (compiledMachine attempts) ([false, false] ++ natural parameter ++ natural 8887896)
      (initial (compiledMachine attempts)) =
    (samplerBatchMemory offlinePlan attempts 838208 0
      (offlineInitialMemory {bits := fun index => if index = 0 then natural parameter ++ natural 8887896 else []})).map
      (fun result => some ((executeLinear publicWireProgram result.1).bits 3,
        (⟨executeLinear publicWireProgram result.1,
          (compiledMachine attempts).size + 1 + (result.2 + publicWireProgram.length + 5), 0⟩ : State))) := by
  let base : Memory := {bits := fun index => if index = 0 then natural parameter ++ natural 8887896 else []}
  let inputMemory : Memory :=
    {(initial (compiledMachine attempts)).memory with
      bits := Function.update (Function.update (initial (compiledMachine attempts)).memory.bits 0
        ([false, false] ++ natural parameter ++ natural 8887896)) 3 []}
  have inputWire : inputMemory.bits 0 = false :: false :: (natural parameter ++ natural 8887896) := by
    simp [inputMemory]
  have dispatched : phaseDispatchMemory inputMemory (natural parameter ++ natural 8887896) = base := by
    dsimp [phaseDispatchMemory, inputMemory, initial, base]
    congr 1
    funext index
    simp only [Function.update_apply]
    split_ifs <;> rfl
  have executed := compiledMachine_setupRun attempts
    (batchStepBudget attempts * 838208 + publicWireProgram.length + 3) inputMemory
    (natural parameter ++ natural 8887896) inputWire
  rw [dispatched] at executed
  have offline : run (offlineMachine attempts)
      (batchStepBudget attempts * 838208 + publicWireProgram.length + 3) ⟨0, base⟩ =
      (samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).map (fun result =>
        some (⟨offlineWireLabel publicWireProgram.length, executeLinear publicWireProgram result.1⟩,
          result.2 + publicWireProgram.length + 3)) := offlineMachine_run attempts base attemptFits
  have joined := executed.trans (congrArg (PMF.map
    (Option.map fun result =>
      (relocateConfiguration (phaseSetupLabels (offlineMachine attempts) (onlineMachine attempts)
        (recordedPublicHandler attempts)) result.1, result.2 + 2))) offline)
  have response := respond_source (compiledMachine attempts)
    ([false, false] ++ natural parameter ++ natural 8887896) (initial (compiledMachine attempts))
    (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3))
    ((samplerBatchMemory offlinePlan attempts 838208 0 (offlineInitialMemory base)).map fun result =>
      (relocateConfiguration (phaseSetupLabels (offlineMachine attempts) (onlineMachine attempts)
        (recordedPublicHandler attempts))
        ⟨offlineWireLabel publicWireProgram.length, executeLinear publicWireProgram result.1⟩,
        result.2 + publicWireProgram.length + 5)) enough ?_
  · rw [response, PMF.map_comp]
    rfl
  · change run (compiledMachine attempts)
      (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3))
      ⟨0, inputMemory⟩ = _
    refine joined.trans ?_
    simp only [PMF.map_comp]
    congr 1


/-- The canonical parser accepts the complete public table from the actual setup response. -/
theorem compiledMachine_setupPublic [FieldCertificate] (attempts parameter : Nat)
    (attemptFits : attempts < 2 ^ 256)
    (enough : (initial (compiledMachine attempts)).spent +
      (2 + (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)) ≤ budget 0) :
    (respond (compiledMachine attempts) ([false, false] ++ natural parameter ++ natural 8887896)
      (initial (compiledMachine attempts))).map
      (fun result => result.bind fun result => publicValue Wire.encoding 8887896 result.1) =
      (SimulatorSampling.offline.total attempts).law.map (fun coin => some (publicSourceTable coin.1)) := by
  rw [compiledMachine_setupResponse attempts parameter attemptFits enough, PMF.map_comp]
  exact offlineMemory_public attempts
    (offlineInitialMemory {bits := fun index => if index = 0 then natural parameter ++ natural 8887896 else []})
    (by simp [offlineInitialMemory]) (by simp [offlineInitialMemory])

/-- The fixed retry count has the canonical setup law within the shared budget. -/
theorem compiledMachine_setupPublic256 [FieldCertificate] (parameter : Nat) :
    (respond (compiledMachine 256) ([false, false] ++ natural parameter ++ natural 8887896)
      (initial (compiledMachine 256))).map
      (fun result => result.bind fun result => publicValue Wire.encoding 8887896 result.1) =
      (SimulatorSampling.offline.total 256).law.map (fun coin => some (publicSourceTable coin.1)) :=
  compiledMachine_setupPublic 256 parameter (by decide) compiledMachine_setupBudget

end
end Kriterion.ArgoMAC.ArithmeticSimulator
