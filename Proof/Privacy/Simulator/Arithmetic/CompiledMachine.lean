import Proof.Privacy.Simulator.Arithmetic.OfflineMachineRun
import Proof.Privacy.Simulator.Arithmetic.OnlineMachine
import Proof.Privacy.Simulator.Arithmetic.PhaseMachineRun

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
noncomputable section
attribute [local irreducible] publicWireProgram offlinePlan

private theorem phaseBudget (setup : Machine) (online : Simulator) (fuel : Nat)
    (bound : setup.size + 1 + fuel ≤ 605084290688)
    (code : online.size ≤ 290305299) (steps : online.secondFuel ≤ 2 ^ 46) :
    phaseSimulatorSize setup online + 1 + (2 + fuel) + (2 + online.secondFuel) ≤ 2 ^ 60 := by
  unfold phaseSimulatorSize
  omega

/-- One table runs setup and encoding under the shared constant allowance. -/
def lazyCompiledMachine : Simulator :=
  phaseSimulator (offlineMachine 256) lazyOnlineMachine
    (batchStepBudget 256 * 838208 + publicWireProgram.length + 3)
    (phaseBudget (offlineMachine 256) lazyOnlineMachine
      (batchStepBudget 256 * 838208 + publicWireProgram.length + 3)
      offlineMachine_budget (by decide) (by decide))

/-- The setup phase preserves the sampler law and leaves the fixed oracle unchanged. -/
theorem lazyCompiledMachine_setupRun [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: false :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.firstFuel memory oracle =
      (samplerBatchMemory offlinePlan 256 838208 0
        (offlineInitialMemory (phaseDispatchMemory memory body))).map fun result =>
        some (executeLinear publicWireProgram result.1, oracle,
          result.2 + publicWireProgram.length + 5) := by
  unfold lazyCompiledMachine
  change simulatorMemoryRun _ (2 + (batchStepBudget 256 * 838208 + publicWireProgram.length + 3)) memory oracle = _
  have setup := offlineMachine_run 256 (phaseDispatchMemory memory body) (by decide)
  have zero (size : Nat) : (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = 0 := by
    apply Fin.ext
    simp
  simp only [zero] at setup
  rw [phaseSimulator_setupMemoryRun _ _ _ _ _ memory body wire oracle, setup, PMF.map_comp]
  simp [Function.comp_def, Nat.add_assoc]

/-- The encoding phase adds two dispatch steps to the fixed-oracle online run. -/
theorem lazyCompiledMachine_onlineRun [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (memory : Memory) (body : List Bool) (wire : memory.bits 0 = false :: true :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    simulatorMemoryRun lazyCompiledMachine lazyCompiledMachine.secondFuel memory oracle =
      (simulatorMemoryRun lazyOnlineMachine (2 ^ 46) (phaseDispatchMemory memory body) oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 2)) := by
  unfold lazyCompiledMachine
  exact phaseSimulator_onlineMemoryRun _ _ _ _ _ memory body wire oracle

end
end Kriterion.ArgoMAC.ArithmeticSimulator
