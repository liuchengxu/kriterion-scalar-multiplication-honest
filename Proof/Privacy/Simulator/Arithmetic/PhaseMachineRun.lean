import Construction.Simulator.PhaseMachine
import Proof.Privacy.Simulator.Arithmetic.AssemblyRun
import Proof.Privacy.Simulator.Arithmetic.PhaseDispatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

def simulatorStart (machine : Simulator) (memory : Memory) : Configuration (machine.size + 1) :=
  ⟨⟨0, Nat.zero_lt_succ machine.size⟩, memory⟩

/-- The protocol retains memory and discards the internal program counter. -/
noncomputable def simulatorMemoryRun [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Simulator) (fuel : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    PMF (Option (Memory × Cryptography.LazyOracle.State FixedIndex EncIndex × Nat)) :=
  (machine.run fuel (simulatorStart machine memory) oracle).map
    (Option.map fun result => (result.1.memory, result.2))

variable [BN254.FieldCertificate]
  {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
  [DecidableEq FixedIndex] [DecidableEq EncIndex]
  (setup : Machine) (online : Simulator) (setupFuel : Nat)
  (within : phaseSimulatorSize setup online + 1 + (2 + setupFuel) + (2 + online.secondFuel) ≤ 2 ^ 60)

/-- The dispatcher consumes two bits and retains all private state. -/
theorem phaseSimulator_dispatch (fuel : Nat) (memory : Memory) (body : List Bool) (encoding : Bool)
    (wire : memory.bits 0 = false :: encoding :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    (phaseSimulator setup online setupFuel within).run (2 + fuel) ⟨0, memory⟩ oracle =
      ((phaseSimulator setup online setupFuel within).run fuel
        ⟨if encoding then phaseSimulatorOnline setup online 0 else phaseSimulatorSetup setup online 0,
          phaseDispatchMemory memory body⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 2)) := by
  apply Simulator.run_prefix
  rw [show 2 + fuel = (fuel + 1) + 1 by omega]
  cases encoding <;>
    simp [run, step, Simulator.arithmetic, phaseSimulator, phaseSimulatorSize,
      phaseSimulatorSetup, phaseSimulatorOnline, phaseDispatchMemory, wire,
      PMF.pure_bind, PMF.map_comp, Function.comp_def]

/-- The setup body retains every arithmetic instruction. -/
theorem phaseSimulator_setup_contains
    (bound : setup.size + 1 + 0 + 0 ≤ 2 ^ 60) :
    ContainsSimulator (phaseSimulator setup online setupFuel within)
      (Simulator.ofMachine setup 0 0 bound) (phaseSimulatorSetup setup online) := by
  intro pc
  have valid : pc.val < setup.size + 1 := pc.isLt
  simp [phaseSimulator, phaseSimulatorSetup, Simulator.ofMachine,
    show ¬ 2 + pc.val = 0 by omega, show ¬ 2 + pc.val = 1 by omega,
    show 2 + pc.val < 3 + setup.size by omega, relocateSimulator]

/-- The online body retains every fixed-oracle instruction. -/
theorem phaseSimulator_online_contains :
    ContainsSimulator (phaseSimulator setup online setupFuel within) online
      (phaseSimulatorOnline setup online) := by
  intro pc
  have valid := pc.isLt
  simp [phaseSimulator, phaseSimulatorOnline,
    show ¬ 3 + setup.size + pc.val = 0 by omega,
    show ¬ 3 + setup.size + pc.val = 1 by omega,
    show ¬ 3 + setup.size + pc.val < 3 + setup.size by omega,
    show 3 + setup.size + pc.val < phaseSimulatorSize setup online by unfold phaseSimulatorSize; omega]

/-- Setup adds two dispatch steps and leaves the fixed oracle unchanged. -/
theorem phaseSimulator_setupRun (fuel : Nat) (memory : Memory) (body : List Bool)
    (wire : memory.bits 0 = false :: false :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    (phaseSimulator setup online setupFuel within).run (2 + fuel) ⟨0, memory⟩ oracle =
      (run setup fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result =>
          (relocateConfiguration (phaseSimulatorSetup setup online) result.1, oracle, result.2 + 2)) := by
  have bound : setup.size + 1 + 0 + 0 ≤ 2 ^ 60 := by unfold phaseSimulatorSize at within; omega
  rw [phaseSimulator_dispatch setup online setupFuel within fuel memory body false wire oracle]
  change ((phaseSimulator setup online setupFuel within).run fuel
    (relocateConfiguration (phaseSimulatorSetup setup online) ⟨0, phaseDispatchMemory memory body⟩) oracle).map _ = _
  rw [relocate_simulator_run _ (Simulator.ofMachine setup 0 0 bound) _
    (phaseSimulator_setup_contains setup online setupFuel within bound), Simulator.ofMachine_run,
    PMF.map_comp, PMF.map_comp]
  simp [Function.comp_def, Option.map_map]
  rfl

/-- Encoding adds two dispatch steps to the online run. -/
theorem phaseSimulator_onlineRun (fuel : Nat) (memory : Memory) (body : List Bool)
    (wire : memory.bits 0 = false :: true :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    (phaseSimulator setup online setupFuel within).run (2 + fuel) ⟨0, memory⟩ oracle =
      (online.run fuel ⟨0, phaseDispatchMemory memory body⟩ oracle).map
        (Option.map fun result =>
          (relocateConfiguration (phaseSimulatorOnline setup online) result.1, result.2.1, result.2.2 + 2)) := by
  rw [phaseSimulator_dispatch setup online setupFuel within fuel memory body true wire oracle]
  change ((phaseSimulator setup online setupFuel within).run fuel
    (relocateConfiguration (phaseSimulatorOnline setup online) ⟨0, phaseDispatchMemory memory body⟩) oracle).map _ = _
  rw [relocate_simulator_run _ online _ (phaseSimulator_online_contains setup online setupFuel within), PMF.map_comp]
  simp [Function.comp_def, Option.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The setup memory law removes only the internal program counter. -/
theorem phaseSimulator_setupMemoryRun (fuel : Nat) (memory : Memory) (body : List Bool)
    (wire : memory.bits 0 = false :: false :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    simulatorMemoryRun (phaseSimulator setup online setupFuel within) (2 + fuel) memory oracle =
      (run setup fuel ⟨0, phaseDispatchMemory memory body⟩).map
        (Option.map fun result => (result.1.memory, oracle, result.2 + 2)) := by
  unfold simulatorMemoryRun simulatorStart
  have zero (size : Nat) : (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = 0 := by
    apply Fin.ext
    simp
  simp only [zero]
  rw [phaseSimulator_setupRun setup online setupFuel within fuel memory body wire oracle, PMF.map_comp]
  simp [Function.comp_def, Option.map_map, relocateConfiguration]

set_option backward.isDefEq.respectTransparency false in
/-- The online memory law adds only the two dispatch steps. -/
theorem phaseSimulator_onlineMemoryRun (fuel : Nat) (memory : Memory) (body : List Bool)
    (wire : memory.bits 0 = false :: true :: body)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) :
    simulatorMemoryRun (phaseSimulator setup online setupFuel within) (2 + fuel) memory oracle =
      (simulatorMemoryRun online fuel (phaseDispatchMemory memory body) oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 2)) := by
  unfold simulatorMemoryRun simulatorStart
  have zero (size : Nat) : (⟨0, Nat.zero_lt_succ size⟩ : Fin (size + 1)) = 0 := by
    apply Fin.ext
    simp
  simp only [zero]
  rw [phaseSimulator_onlineRun setup online setupFuel within fuel memory body wire oracle,
    PMF.map_comp, PMF.map_comp]
  simp [Function.comp_def, Option.map_map, relocateConfiguration]

end Kriterion.ArgoMAC.ArithmeticSimulator
