import Proof.Privacy.Simulator.Arithmetic.OfflineMachineRun

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
attribute [local irreducible] publicWireProgram offlinePlan Wire.encoding publicValue

/-- The complete offline machine returns the sampled public table through the canonical parser. -/
theorem offlineMachine_public [FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) (empty : base.bits 3 = []) :
    (run (offlineMachine attempts) (batchStepBudget attempts * 838208 + publicWireProgram.length + 3)
      ⟨⟨0, Nat.zero_lt_succ _⟩, base⟩).map
      (fun result => result.bind fun result => publicValue Wire.encoding 8887896 (result.1.memory.bits 3)) =
      (SimulatorSampling.offline.total attempts).law.map (fun coin => some (publicSourceTable coin.1)) := by
  rw [offlineMachine_run attempts base countFits, PMF.map_comp]
  simp only [Function.comp_def, Option.bind_some]
  exact offlineMemory_public attempts (offlineInitialMemory base)
    (by simp [offlineInitialMemory]) empty

/-- The default machine has the complete typed output law within its concrete budget. -/
theorem offlineMachine_256_public [FieldCertificate] (base : Memory) (empty : base.bits 3 = []) :
    (run (offlineMachine 256) (batchStepBudget 256 * 838208 + publicWireProgram.length + 3)
      ⟨⟨0, Nat.zero_lt_succ _⟩, base⟩).map
      (fun result => result.bind fun result => publicValue Wire.encoding 8887896 (result.1.memory.bits 3)) =
      (SimulatorSampling.offline.total 256).law.map (fun coin => some (publicSourceTable coin.1)) :=
  offlineMachine_public 256 base (by decide) empty

end Kriterion.ArgoMAC.ArithmeticSimulator
