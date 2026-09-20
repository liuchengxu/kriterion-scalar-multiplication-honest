import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.ReversePairs

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the reverse transposition scan and supplies its return instruction. -/
def ContainsReverseSwapTable (host : Machine) (labels : Fin 15 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 15, pc ≠ 13 → host.code[(labels pc).val] =
    relocate labels (reverseSwapTable.code[pc.val]'(by exact pc.isLt))

/-- One machine iteration applies the selected transposition. -/
theorem reverseSwapBlock_step [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 15 → Fin (host.size + 1)) (present : ContainsReverseSwapTable host labels)
    (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256) (one : memory.registers 14 = 1#256) (three : memory.registers 15 = 3#256) :
    runPrefix host (fuel + reverseSwapCost memory) ⟨labels 1, memory⟩ =
      (runPrefix host fuel ⟨labels 1, reverseSwapMemory memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + reverseSwapCost memory)) := by
  by_cases left : memory.registers 8 = memory.ram (memory.registers 9)
  · simp [reverseSwapCost, left, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, reverseSwapTable, counter, one, three, Arithmetic.eval,
      reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
      Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg]
    try rfl
  · by_cases right : memory.registers 8 = memory.ram (memory.registers 9 + 1#256)
    · have mismatch : memory.ram (memory.registers 9 + 1#256) ≠ memory.ram (memory.registers 9) := by
        intro equal
        exact left (right.trans equal)
      simp [reverseSwapCost, left, right, mismatch, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, reverseSwapTable, counter, one, three, Arithmetic.eval,
        reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg]
      try rfl
    · simp [reverseSwapCost, left, right, runPrefix, step, present 1 (by decide), present 2 (by decide), present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide), present 11 (by decide), present 12 (by decide), relocate, reverseSwapTable, counter, one, three, Arithmetic.eval,
        reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg, Function.update_eq_self]
      try rfl

/-- The loop returns before its final halt and retains the exact cost. -/
theorem reverseSwapBlock_loop [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 15 → Fin (host.size + 1)) (present : ContainsReverseSwapTable host labels)
    (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) (three : memory.registers 15 = 3#256) :
    runPrefix host ((reverseSwapScan count memory).2 - 1) ⟨labels 1, memory⟩ =
      PMF.pure (some (false, ⟨labels 13, (reverseSwapScan count memory).1⟩, (reverseSwapScan count memory).2 - 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [reverseSwapScan, runPrefix, step, present 1 (by decide), relocate, reverseSwapTable, counter, PMF.pure_map]
      try rfl
  | succ count ih =>
      have positive := (reverseSwapScan_cost count (reverseSwapMemory memory)).1
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
      simp only [reverseSwapScan]
      rw [show (reverseSwapScan count (reverseSwapMemory memory)).2 + reverseSwapCost memory - 1 =
        ((reverseSwapScan count (reverseSwapMemory memory)).2 - 1) + reverseSwapCost memory by omega,
        reverseSwapBlock_step host labels present _ memory nonzero one three,
        ih (reverseSwapMemory memory) (by omega) (by simp [reverseSwapMemory, counter, decrement])
          (by simp [reverseSwapMemory, one]) (by simp [reverseSwapMemory, three]), PMF.pure_map]
      try rfl


/-- The host initializes both increments in two instructions. -/
theorem reverseSwapBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 15 → Fin (host.size + 1)) (present : ContainsReverseSwapTable host labels)
    (memory : Memory) :
    runPrefix host 2 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 1, reverseSwapInitial memory⟩, 2)) := by
  simp [runPrefix, step, present 0 (by decide), present 14 (by decide),
    reverseSwapTable, relocate, reverseSwapInitial, PMF.pure_map]

/-- The complete reverse block returns the exact state and prefix cost. -/
theorem reverseSwapBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 15 → Fin (host.size + 1)) (present : ContainsReverseSwapTable host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    runPrefix host ((reverseSwapScan count (reverseSwapInitial memory)).2 + 1) ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 13, (reverseSwapScan count (reverseSwapInitial memory)).1⟩,
        (reverseSwapScan count (reverseSwapInitial memory)).2 + 1)) := by
  have positive := (reverseSwapScan_cost count (reverseSwapInitial memory)).1
  have total : (reverseSwapScan count (reverseSwapInitial memory)).2 + 1 =
      2 + ((reverseSwapScan count (reverseSwapInitial memory)).2 - 1) := by omega
  conv_lhs => arg 2; rw [total]
  rw [prefix_add, reverseSwapBlock_setup host labels present memory, PMF.pure_bind]
  dsimp only
  rw [reverseSwapBlock_loop host labels present count (reverseSwapInitial memory) fits
    (by simp [reverseSwapInitial, counter]) (by simp [reverseSwapInitial])
    (by simp [reverseSwapInitial]), PMF.pure_map]
  simp only [Option.map_some]
  rw [show (reverseSwapScan count (reverseSwapInitial memory)).2 - 1 + 2 =
    (reverseSwapScan count (reverseSwapInitial memory)).2 + 1 by omega]

/-- The reverse block passes its complete memory and actual cost to the continuation. -/
theorem reverseSwapBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 15 → Fin (host.size + 1)) (present : ContainsReverseSwapTable host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((reverseSwapScan count (reverseSwapInitial memory)).2 + 1 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 13, (reverseSwapScan count (reverseSwapInitial memory)).1⟩).map
        (Option.map fun result => (result.1, result.2 + ((reverseSwapScan count (reverseSwapInitial memory)).2 + 1))) := by
  rw [run_after_prefix, reverseSwapBlock_prefix host labels present count memory fits counter,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
