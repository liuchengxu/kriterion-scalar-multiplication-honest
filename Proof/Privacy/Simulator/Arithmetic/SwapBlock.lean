import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.SwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the transposition scan and supplies its return instruction. -/
def ContainsSwapTable (host : Machine) (labels : Fin 14 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 14, pc ≠ 13 → host.code[(labels pc).val] =
    relocate labels (swapTable.code[pc.val]'(by exact pc.isLt))

/-- One machine iteration applies the selected transposition. -/
theorem swapBlock_step [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 14 → Fin (host.size + 1)) (present : ContainsSwapTable host labels)
    (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256) (one : memory.registers 14 = 1#256) :
    runPrefix host (fuel + swapCost memory) ⟨labels 1, memory⟩ =
      (runPrefix host fuel ⟨labels 1, swapMemory memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + swapCost memory)) := by
  by_cases left : memory.registers 8 = memory.ram (memory.registers 9)
  · simp [swapCost, left, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, swapTable, counter, one, Arithmetic.eval,
      swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
      Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc]
    try rfl
  · by_cases right : memory.registers 8 = memory.ram (memory.registers 9 + 1#256)
    · have mismatch : memory.ram (memory.registers 9 + 1#256) ≠ memory.ram (memory.registers 9) := by
        intro equal
        exact left (right.trans equal)
      simp [swapCost, left, right, mismatch, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, swapTable, counter, one, Arithmetic.eval,
        swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc]
      try rfl
    · simp [swapCost, left, right, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, swapTable, counter, one, Arithmetic.eval,
        swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, Function.update_eq_self]
      try rfl

/-- The loop returns before its final halt and retains the exact cost. -/
theorem swapBlock_loop [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 14 → Fin (host.size + 1)) (present : ContainsSwapTable host labels)
    (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) :
    runPrefix host ((swapScan count memory).2 - 1) ⟨labels 1, memory⟩ =
      PMF.pure (some (false, ⟨labels 13, (swapScan count memory).1⟩, (swapScan count memory).2 - 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [swapScan, runPrefix, step, present 1 (by decide), relocate, swapTable, counter, PMF.pure_map]
      try rfl
  | succ count ih =>
      have positive := (swapScan_cost count (swapMemory memory)).1
      have nonzero : memory.registers 10 ≠ 0#256 := by
        rw [counter]
        intro equal
        have values := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at values
        change count + 1 = 0 at values
        omega
      have decrement : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
        rw [BitVec.ofNat_add]
        simp
      simp only [swapScan]
      rw [show (swapScan count (swapMemory memory)).2 + swapCost memory - 1 =
        ((swapScan count (swapMemory memory)).2 - 1) + swapCost memory by omega,
        swapBlock_step host labels present _ memory nonzero one,
        ih (swapMemory memory) (by omega) (by simp [swapMemory, counter, decrement])
          (by simp [swapMemory, one]), PMF.pure_map]
      try rfl

/-- The host initializes the increment in one instruction. -/
theorem swapBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 14 → Fin (host.size + 1)) (present : ContainsSwapTable host labels)
    (memory : Memory) :
    runPrefix host 1 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 1, swapInitial memory⟩, 1)) := by
  simp [runPrefix, step, present 0 (by decide), swapTable, relocate, swapInitial, PMF.pure_map]

/-- The complete host block returns the exact transposition state and prefix cost. -/
theorem swapBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 14 → Fin (host.size + 1)) (present : ContainsSwapTable host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    runPrefix host (swapScan count (swapInitial memory)).2 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 13, (swapScan count (swapInitial memory)).1⟩,
        (swapScan count (swapInitial memory)).2)) := by
  have positive := (swapScan_cost count (swapInitial memory)).1
  have total : (swapScan count (swapInitial memory)).2 =
      1 + ((swapScan count (swapInitial memory)).2 - 1) := by omega
  conv_lhs => arg 2; rw [total]
  rw [prefix_add, swapBlock_setup host labels present memory, PMF.pure_bind]
  dsimp only
  rw [swapBlock_loop host labels present count (swapInitial memory) fits
    (by simp [swapInitial, counter]) (by simp [swapInitial]), PMF.pure_map]
  simp only [Option.map_some]
  rw [show (swapScan count (swapInitial memory)).2 - 1 + 1 =
    (swapScan count (swapInitial memory)).2 by omega]

/-- The transposition block passes its complete memory and actual cost to the continuation. -/
theorem swapBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 14 → Fin (host.size + 1)) (present : ContainsSwapTable host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((swapScan count (swapInitial memory)).2 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 13, (swapScan count (swapInitial memory)).1⟩).map
        (Option.map fun result => (result.1, result.2 + (swapScan count (swapInitial memory)).2)) := by
  rw [run_after_prefix, swapBlock_prefix host labels present count memory fits counter,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
