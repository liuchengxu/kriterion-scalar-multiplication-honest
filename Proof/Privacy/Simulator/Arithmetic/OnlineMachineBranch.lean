import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The tag test keeps its loaded word in register zero. -/
def onlineTagMemory (memory : Memory) : Memory :=
  {memory with registers := Function.update memory.registers 0 (memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)))}

/-- The tag test selects its absent-output or present-output return. -/
def onlineBranchReturn (memory : Memory) (absent present : Fin 290305300) : Fin 290305300 :=
  if memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0 then absent else present

/-- The first tag test has exactly three fixed instructions. -/
theorem onlineMachine_firstBranch (attempts : Nat) :
    (onlineMachine attempts).code[13618]'(by change 13618 < 290305300; decide) = .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 13619 ∧
    (onlineMachine attempts).code[13619]'(by change 13619 < 290305300; decide) = .load 0 0 13620 ∧
    (onlineMachine attempts).code[13620]'(by change 13620 < 290305300; decide) = .branch 0 1435659 13621 := by
  change (onlineMachineCode attempts)[13618] = _ ∧ (onlineMachineCode attempts)[13619] = _ ∧
    (onlineMachineCode attempts)[13620] = _
  simp only [onlineMachineCode_get]
  exact ⟨rfl, rfl, rfl⟩

/-- The second tag test has exactly three fixed instructions. -/
theorem onlineMachine_secondBranch (attempts : Nat) :
    (onlineMachine attempts).code[2751382]'(by change 2751382 < 290305300; decide) = .constant 0 (BitVec.ofNat 256 (onlineInputBase + 2)) 2751383 ∧
    (onlineMachine attempts).code[2751383]'(by change 2751383 < 290305300; decide) = .load 0 0 2751384 ∧
    (onlineMachine attempts).code[2751384]'(by change 2751384 < 290305300; decide) = .branch 0 290104636 2751385 := by
  change (onlineMachineCode attempts)[2751382] = _ ∧ (onlineMachineCode attempts)[2751383] = _ ∧
    (onlineMachineCode attempts)[2751384] = _
  simp only [onlineMachineCode_get]
  exact ⟨rfl, rfl, rfl⟩

private theorem tagBranch_prefix [BN254.FieldCertificate] (host : Machine)
    (entry next last absent present : Fin (host.size + 1)) (memory : Memory) (address : Word)
    (code : host.code[entry.val] = .constant 0 address next ∧
      host.code[next.val] = .load 0 0 last ∧ host.code[last.val] = .branch 0 absent present) :
    runPrefix host 3 ⟨entry, memory⟩ =
      PMF.pure (some (false,
        ⟨if memory.ram address = 0 then absent else present,
          {memory with registers := Function.update memory.registers 0 (memory.ram address)}⟩, 3)) := by
  simp [runPrefix, step, code.1, code.2.1, code.2.2, Function.update_idem, PMF.pure_map]

private theorem tagBranch_continue [BN254.FieldCertificate] (host : Machine)
    (entry next last absent present : Fin (host.size + 1)) (memory : Memory) (address : Word) (fuel : Nat)
    (code : host.code[entry.val] = .constant 0 address next ∧
      host.code[next.val] = .load 0 0 last ∧ host.code[last.val] = .branch 0 absent present) :
    run host (3 + fuel) ⟨entry, memory⟩ =
      (run host fuel ⟨if memory.ram address = 0 then absent else present,
        {memory with registers := Function.update memory.registers 0 (memory.ram address)}⟩).map
          (Option.map fun result => (result.1, result.2 + 3)) := by
  rw [run_after_prefix, tagBranch_prefix host entry next last absent present memory address code, PMF.pure_bind]

/-- The first tag test passes its exact state and charge to the selected path. -/
theorem onlineMachine_firstBranch_continue [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (3 + fuel) ⟨13618, memory⟩ =
      (run (onlineMachine attempts) fuel
        ⟨onlineBranchReturn memory 1435659 13621, onlineTagMemory memory⟩).map
          (Option.map fun result => (result.1, result.2 + 3)) :=
  tagBranch_continue (onlineMachine attempts) 13618 13619 13620 1435659 13621 memory
    (BitVec.ofNat 256 (onlineInputBase + 2)) fuel (onlineMachine_firstBranch attempts)

/-- The second tag test passes its exact state and charge to the selected path. -/
theorem onlineMachine_secondBranch_continue [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (3 + fuel) ⟨2751382, memory⟩ =
      (run (onlineMachine attempts) fuel
        ⟨onlineBranchReturn memory 290104636 2751385, onlineTagMemory memory⟩).map
          (Option.map fun result => (result.1, result.2 + 3)) :=
  tagBranch_continue (onlineMachine attempts) 2751382 2751383 2751384 290104636 2751385 memory
    (BitVec.ofNat 256 (onlineInputBase + 2)) fuel (onlineMachine_secondBranch attempts)

/-- The fixed-oracle simulator charges its firstBranch test and keeps oracle state. -/
theorem lazyOnlineMachine_firstBranch_continue [BN254.FieldCertificate]
    (fuel : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (3 + fuel) ⟨13618, memory⟩ oracle =
      (lazyOnlineMachine.run fuel
        ⟨onlineBranchReturn memory 1435659 13621, onlineTagMemory memory⟩ oracle).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  apply Simulator.run_prefix lazyOnlineMachine 3 fuel _ _ oracle
  apply tagBranch_continue lazyOnlineMachine.arithmetic 13618 13619 13620 1435659 13621 memory
    (BitVec.ofNat 256 (onlineInputBase + 2)) fuel
  rw [lazyOnlineMachine_private 13618 (by decide), lazyOnlineMachine_private 13619 (by decide),
    lazyOnlineMachine_private 13620 (by decide)]
  exact onlineMachine_firstBranch 256

/-- The fixed-oracle simulator charges its secondBranch test and keeps oracle state. -/
theorem lazyOnlineMachine_secondBranch_continue [BN254.FieldCertificate]
    (fuel : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    lazyOnlineMachine.run (3 + fuel) ⟨2751382, memory⟩ oracle =
      (lazyOnlineMachine.run fuel
        ⟨onlineBranchReturn memory 290104636 2751385, onlineTagMemory memory⟩ oracle).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  apply Simulator.run_prefix lazyOnlineMachine 3 fuel _ _ oracle
  apply tagBranch_continue lazyOnlineMachine.arithmetic 2751382 2751383 2751384 290104636 2751385 memory
    (BitVec.ofNat 256 (onlineInputBase + 2)) fuel
  rw [lazyOnlineMachine_private 2751382 (by decide), lazyOnlineMachine_private 2751383 (by decide),
    lazyOnlineMachine_private 2751384 (by decide)]
  exact onlineMachine_secondBranch 256

end Kriterion.ArgoMAC.ArithmeticSimulator
