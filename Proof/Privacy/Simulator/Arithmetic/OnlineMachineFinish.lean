import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLinear
import Proof.Privacy.Simulator.Arithmetic.FixedContinuation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The online machine has two terminal halt instructions, and they mean
different things. `290305298` is the pc of a run that completed the label
output; `290305299` is the pc of a run the public sampler cut off before it. The
machine protocol accepts a run exactly when its pc is `290305298`, so the two
must stay distinct: a single halt slot makes a cut-off run parse as a completed
one, and `OnlineGateJointMachine`/`OnlineNullJointSource` then state something
false. -/
theorem onlineMachine_halts (attempts : Nat) :
    (onlineMachineCode attempts)[290305298] = .halt ∧
      (onlineMachineCode attempts)[290305299] = .halt := by
  simp only [onlineMachineCode_get]
  exact ⟨rfl, rfl⟩

/-- The final memory contains the complete original-label output. -/
noncomputable def onlineFinalMemory (memory : Memory) : Memory :=
  executeLinear selectedLabelsCode (executeLinear onlineLabelSetup memory)

private theorem haltAt [BN254.FieldCertificate] (host : Machine) (pc : Fin (host.size + 1))
    (code : host.code[pc.val] = .halt) (fuel : Nat) (memory : Memory) :
    run host (fuel + 1) ⟨pc, memory⟩ = PMF.pure (some (⟨pc, memory⟩, 1)) := by
  simp [run, step, code]

private theorem finishRun [BN254.FieldCertificate] (host : Machine)
    (entry middle last : Fin (host.size + 1)) (initial prepared final : Memory) (fuel firstCost secondCost : Nat)
    (setup : ∀ reserve, run host (firstCost + reserve) ⟨entry, initial⟩ =
      (run host reserve ⟨middle, prepared⟩).map (Option.map fun result => (result.1, result.2 + firstCost)))
    (labels : ∀ reserve, run host (secondCost + reserve) ⟨middle, prepared⟩ =
      (run host reserve ⟨last, final⟩).map (Option.map fun result => (result.1, result.2 + secondCost)))
    (halted : host.code[last.val] = .halt) :
    run host (firstCost + secondCost + 1 + fuel) ⟨entry, initial⟩ =
      PMF.pure (some (⟨last, final⟩, 1 + secondCost + firstCost)) := by
  rw [show firstCost + secondCost + 1 + fuel = firstCost + (secondCost + (fuel + 1)) by omega, setup, labels,
    haltAt host last halted fuel final, PMF.pure_map, PMF.pure_map]
  rfl

/-- The final fixed label block charges its setup, body, and halt.
It ends on the first terminal slot, the completed-run pc. -/
theorem onlineMachine_finish [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (200663 + fuel) ⟨290104636, memory⟩ =
      PMF.pure (some (⟨290305298, onlineFinalMemory memory⟩, 200663)) := by
  apply finishRun (onlineMachine attempts) 290104636 290104638 290305298 memory
    (executeLinear onlineLabelSetup memory) (onlineFinalMemory memory) fuel 2 200660
  · intro reserve
    exact linear_continue (onlineMachine attempts) onlineLabelSetup
      (onlineBodyLabels 290104636 2 (by decide) 290104638)
      (onlineMachine_labelSetup attempts) memory reserve
  · intro reserve
    exact selectedLabelsHost_continue (onlineMachine attempts)
      (onlineBodyLabels 290104638 200660 (by decide) 290305298)
      (onlineMachine_labels attempts) (executeLinear onlineLabelSetup memory) reserve
  · exact (onlineMachine_halts attempts).1

/-- A cutoff stops before the final label output and charges one halt instruction.
It lands on the second terminal slot, which the machine protocol reads as
`aborted` rather than as a completed run. -/
theorem onlineMachine_cutoff [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (1 + fuel) ⟨290305299, memory⟩ =
      PMF.pure (some (⟨290305299, memory⟩, 1)) := by
  rw [Nat.add_comm 1 fuel]
  exact haltAt (onlineMachine attempts) 290305299 (onlineMachine_halts attempts).2 fuel memory

/-- Any positive cutoff reserve returns the exact cutoff state. -/
theorem onlineMachine_cutoffClosed [BN254.FieldCertificate] (attempts reserve : Nat) (memory : Memory)
    (positive : 0 < reserve) :
    ClosedRun (onlineMachine attempts) 290305299 memory reserve
      (PMF.pure (⟨290305299, memory⟩, 1)) := by
  intro fuel
  have amount : reserve + fuel = 1 + (reserve - 1 + fuel) := by omega
  rw [amount, onlineMachine_cutoff, PMF.pure_map]

/-- The arithmetic projection computes the final output without an oracle instruction. -/
theorem lazyOnlineMachine_finish_arithmetic [BN254.FieldCertificate] (fuel : Nat) (memory : Memory) :
    run lazyOnlineMachine.arithmetic (200663 + fuel) ⟨290104636, memory⟩ =
      PMF.pure (some (⟨290305298, onlineFinalMemory memory⟩, 200663)) := by
  apply finishRun lazyOnlineMachine.arithmetic 290104636 290104638 290305298 memory
    (executeLinear onlineLabelSetup memory) (onlineFinalMemory memory) fuel 2 200660
  · intro reserve
    exact linear_continue lazyOnlineMachine.arithmetic onlineLabelSetup
      (onlineBodyLabels 290104636 2 (by decide) 290104638)
      (lazyOnlineMachine_linear _ _ (onlineMachine_labelSetup 256) (by
        intro index inside
        unfold onlineBodyLabels
        split <;> (try dsimp only) <;>
          exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩)) memory reserve
  · intro reserve
    exact selectedLabelsHost_continue lazyOnlineMachine.arithmetic
      (onlineBodyLabels 290104638 200660 (by decide) 290305298)
      (lazyOnlineMachine_linear _ _ (onlineMachine_labels 256) (by
        intro index inside
        unfold onlineBodyLabels
        split <;> (try dsimp only) <;>
          exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩))
      (executeLinear onlineLabelSetup memory) reserve
  · rw [lazyOnlineMachine_private 290305298 (by decide)]
    exact (onlineMachine_halts 256).1

private theorem simulator_haltAt [BN254.FieldCertificate] (host : Simulator)
    (pc : Fin (host.size + 1)) (code : host.code[pc.val] = .compute .halt)
    (fuel : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    host.run (fuel + 1) ⟨pc, memory⟩ oracle = PMF.pure (some (⟨pc, memory⟩, oracle, 1)) := by
  simp [Simulator.run, Simulator.step, code, step, Simulator.arithmetic, PMF.pure_bind,
    PMF.bind_map]

set_option maxRecDepth 4096 in
/-- The simulator returns its final labels with a fixed charge and unchanged oracle state. -/
theorem lazyOnlineMachine_finish [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (200663 + fuel) ⟨290104636, memory⟩ oracle =
      PMF.pure (some (⟨290305298, onlineFinalMemory memory⟩, oracle, 200663)) := by
  rw [Simulator.run_arithmetic_prefix, lazyOnlineMachine_finish_arithmetic, PMF.pure_bind]
  have halted : lazyOnlineMachine.code[290305298]'(by decide) = .compute .halt := by
    change lazyOnlineMachine.code[(290305298 : Fin 290305300).val] = _
    rw [lazyOnlineMachine_code]
    rfl
  simp only [show 200663 + fuel - 200663 + 1 = fuel + 1 by omega]
  rw [simulator_haltAt lazyOnlineMachine 290305298 halted fuel (onlineFinalMemory memory) oracle,
    PMF.pure_map]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
