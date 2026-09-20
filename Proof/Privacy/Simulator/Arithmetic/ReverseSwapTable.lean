import Construction.Simulator.ReverseSwapTable
import Proof.Privacy.Simulator.Arithmetic.Blocks
import Proof.Privacy.Simulator.OperationalOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The RAM source agrees with the sparse oracle's transposition list. -/
theorem applyReverseTableSwaps_source (pairs : List (Word × Word)) (ram : Word → Word)
    (address value : Word) (represented : RepresentsReversePairs ram address pairs) :
    applyReverseTableSwaps pairs.length ram address value = Security.OperationalOracle.swaps pairs value := by
  induction pairs generalizing address value with
  | nil => rfl
  | cons pair rest ih =>
      rcases represented with ⟨left, right, tail⟩
      simpa [applyReverseTableSwaps, left, right] using ih (address - 2#256)
        (Equiv.swap pair.1 pair.2 value) tail

/-- Each swap step records the complete register effect. -/
def reverseSwapMemory (memory : Memory) : Memory :=
  let left := memory.ram (memory.registers 9)
  let right := memory.ram (memory.registers 9 + 1#256)
  let value := memory.registers 8
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update memory.registers 11 left) 12 right)
        13 (if value = left then 0 else value ^^^ right))
        8 (Equiv.swap left right value)) 9 (memory.registers 9 - 2#256)) 10 (memory.registers 10 - 1#256) }

/-- A step charges every comparison and every selected branch. -/
def reverseSwapCost (memory : Memory) : Nat :=
  if memory.registers 8 = memory.ram (memory.registers 9) then 9
  else if memory.registers 8 = memory.ram (memory.registers 9 + 1#256) then 11 else 10

/-- The scan returns the exact memory and executed cost. -/
def reverseSwapScan : Nat → Memory → Memory × Nat
  | 0, memory => (memory, 2)
  | count + 1, memory =>
      let result := reverseSwapScan count (reverseSwapMemory memory)
      (result.1, result.2 + reverseSwapCost memory)

/-- Each swap step uses at most eleven instructions. -/
theorem reverseSwapCost_bounds (memory : Memory) : 9 ≤ reverseSwapCost memory ∧ reverseSwapCost memory ≤ 11 := by
  unfold reverseSwapCost
  split
  · omega
  · split <;> omega

/-- The full scan includes its final halt and uses at most eleven instructions per pair. -/
theorem reverseSwapScan_cost (count : Nat) (memory : Memory) :
    1 ≤ (reverseSwapScan count memory).2 ∧ (reverseSwapScan count memory).2 ≤ 11 * count + 2 := by
  induction count generalizing memory with
  | zero => simp [reverseSwapScan]
  | succ count ih =>
      have previous := ih (reverseSwapMemory memory)
      have current := reverseSwapCost_bounds memory
      dsimp [reverseSwapScan]
      omega

/-- One machine iteration applies the selected transposition. -/
theorem reverseSwapTable_step [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256) (one : memory.registers 14 = 1#256) (three : memory.registers 15 = 3#256) :
    runPrefix reverseSwapTable (fuel + reverseSwapCost memory) ⟨1, memory⟩ =
      (runPrefix reverseSwapTable fuel ⟨1, reverseSwapMemory memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + reverseSwapCost memory)) := by
  by_cases left : memory.registers 8 = memory.ram (memory.registers 9)
  · simp [reverseSwapCost, left, runPrefix, step, reverseSwapTable, counter, one, three, Arithmetic.eval,
      reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
      Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg]
    rfl
  · by_cases right : memory.registers 8 = memory.ram (memory.registers 9 + 1#256)
    · have mismatch : memory.ram (memory.registers 9 + 1#256) ≠ memory.ram (memory.registers 9) := by
        intro equal
        exact left (right.trans equal)
      simp [reverseSwapCost, left, right, mismatch, runPrefix, step, reverseSwapTable, counter, one, three, Arithmetic.eval,
        reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg]
      rfl
    · simp [reverseSwapCost, left, right, runPrefix, step, reverseSwapTable, counter, one, three, Arithmetic.eval,
        reverseSwapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, sub_eq_add_neg, Function.update_eq_self]
      rfl

/-- The memory source returns the RAM transposition result. -/
theorem reverseSwapScan_source (count : Nat) (memory : Memory) :
    (reverseSwapScan count memory).1.registers 8 =
      applyReverseTableSwaps count memory.ram (memory.registers 9) (memory.registers 8) := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      simp only [reverseSwapScan]
      rw [ih]
      simp [reverseSwapMemory, applyReverseTableSwaps]

/-- The transposition scan preserves every stack and every RAM cell. -/
theorem reverseSwapScan_data (count : Nat) (memory : Memory) :
    (reverseSwapScan count memory).1.bits = memory.bits ∧ (reverseSwapScan count memory).1.ram = memory.ram := by
  induction count generalizing memory with
  | zero => simp [reverseSwapScan]
  | succ count ih => exact ih (reverseSwapMemory memory)


/-- The loop returns before its final halt and retains the exact cost. -/
theorem reverseSwapTable_loop [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) (three : memory.registers 15 = 3#256) :
    runPrefix reverseSwapTable ((reverseSwapScan count memory).2 - 1) ⟨1, memory⟩ =
      PMF.pure (some (false, ⟨13, (reverseSwapScan count memory).1⟩, (reverseSwapScan count memory).2 - 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [reverseSwapScan, runPrefix, step, reverseSwapTable, counter, PMF.pure_map]
      rfl
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
        reverseSwapTable_step _ memory nonzero one three,
        ih (reverseSwapMemory memory) (by omega) (by simp [reverseSwapMemory, counter, decrement])
          (by simp [reverseSwapMemory, one]) (by simp [reverseSwapMemory, three]), PMF.pure_map]
      rfl


/-- The entry stores the forward read increment and the backward pair stride. -/
def reverseSwapInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update memory.registers 15 3) 14 1 }

/-- The reverse machine retains its complete result and actual instruction count. -/
theorem reverseSwapTable_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    run reverseSwapTable ((reverseSwapScan count (reverseSwapInitial memory)).2 + 2) ⟨0, memory⟩ =
      PMF.pure (some (⟨13, (reverseSwapScan count (reverseSwapInitial memory)).1⟩,
        (reverseSwapScan count (reverseSwapInitial memory)).2 + 2)) := by
  have loop := reverseSwapTable_loop count (reverseSwapInitial memory) fits
    (by simp [reverseSwapInitial, counter]) (by simp [reverseSwapInitial])
    (by simp [reverseSwapInitial])
  have positive := (reverseSwapScan_cost count (reverseSwapInitial memory)).1
  have setup (fuel : Nat) : run reverseSwapTable (fuel + 2) ⟨0, memory⟩ =
      (run reverseSwapTable fuel ⟨1, reverseSwapInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
    simp [run, step, reverseSwapTable, reverseSwapInitial, PMF.map_comp, Option.map_map,
      Function.comp_def, Nat.add_assoc]
    rfl
  rw [setup]
  have remaining : (reverseSwapScan count (reverseSwapInitial memory)).2 =
      ((reverseSwapScan count (reverseSwapInitial memory)).2 - 1) + 1 := by omega
  conv_lhs => arg 2; rw [remaining, run_after_prefix, loop, PMF.pure_bind]
  simp [run, step, reverseSwapTable, PMF.pure_map]
  rw [show 1 + ((reverseSwapScan count (reverseSwapInitial memory)).2 - 1) + 2 =
    (reverseSwapScan count (reverseSwapInitial memory)).2 + 2 by omega]

/-- The reverse table includes fifteen instructions and two entry instructions. -/
theorem reverseSwapTable_budget (count : Nat) (memory : Memory) :
    reverseSwapTable.size + 1 + ((reverseSwapScan count (reverseSwapInitial memory)).2 + 2) ≤
      11 * count + 19 := by
  have bound := (reverseSwapScan_cost count (reverseSwapInitial memory)).2
  change 14 + 1 + ((reverseSwapScan count (reverseSwapInitial memory)).2 + 2) ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
