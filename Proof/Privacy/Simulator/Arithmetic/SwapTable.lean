import Construction.Simulator.SwapTable
import Proof.Privacy.Simulator.Arithmetic.Blocks
import Proof.Privacy.Simulator.OperationalOracle

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The RAM source agrees with the sparse oracle's transposition list. -/
theorem applyTableSwaps_source (pairs : List (Word × Word)) (ram : Word → Word)
    (address value : Word) (represented : RepresentsPairs ram address pairs) :
    applyTableSwaps pairs.length ram address value = Security.OperationalOracle.swaps pairs value := by
  induction pairs generalizing address value with
  | nil => rfl
  | cons pair rest ih =>
      rcases represented with ⟨left, right, tail⟩
      simpa [applyTableSwaps, left, right] using ih (address + 2#256)
        (Equiv.swap pair.1 pair.2 value) tail

/-- Each swap step records the complete register effect. -/
def swapMemory (memory : Memory) : Memory :=
  let left := memory.ram (memory.registers 9)
  let right := memory.ram (memory.registers 9 + 1#256)
  let value := memory.registers 8
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update memory.registers 11 left) 12 right)
        13 (if value = left then 0 else value ^^^ right))
        8 (Equiv.swap left right value)) 9 (memory.registers 9 + 2#256)) 10 (memory.registers 10 - 1#256) }

/-- A step charges every comparison and every selected branch. -/
def swapCost (memory : Memory) : Nat :=
  if memory.registers 8 = memory.ram (memory.registers 9) then 9
  else if memory.registers 8 = memory.ram (memory.registers 9 + 1#256) then 11 else 10

/-- The scan returns the exact memory and executed cost. -/
def swapScan : Nat → Memory → Memory × Nat
  | 0, memory => (memory, 2)
  | count + 1, memory =>
      let result := swapScan count (swapMemory memory)
      (result.1, result.2 + swapCost memory)

/-- Each swap step uses at most eleven instructions. -/
theorem swapCost_bounds (memory : Memory) : 9 ≤ swapCost memory ∧ swapCost memory ≤ 11 := by
  unfold swapCost
  split
  · omega
  · split <;> omega

/-- The full scan includes its final halt and uses at most eleven instructions per pair. -/
theorem swapScan_cost (count : Nat) (memory : Memory) :
    1 ≤ (swapScan count memory).2 ∧ (swapScan count memory).2 ≤ 11 * count + 2 := by
  induction count generalizing memory with
  | zero => simp [swapScan]
  | succ count ih =>
      have previous := ih (swapMemory memory)
      have current := swapCost_bounds memory
      dsimp [swapScan]
      omega

/-- One machine iteration applies the selected transposition. -/
theorem swapTable_step [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256) (one : memory.registers 14 = 1#256) :
    runPrefix swapTable (fuel + swapCost memory) ⟨1, memory⟩ =
      (runPrefix swapTable fuel ⟨1, swapMemory memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + swapCost memory)) := by
  by_cases left : memory.registers 8 = memory.ram (memory.registers 9)
  · simp [swapCost, left, runPrefix, step, swapTable, counter, one, Arithmetic.eval,
      swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
      Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc]
    rfl
  · by_cases right : memory.registers 8 = memory.ram (memory.registers 9 + 1#256)
    · have mismatch : memory.ram (memory.registers 9 + 1#256) ≠ memory.ram (memory.registers 9) := by
        intro equal
        exact left (right.trans equal)
      simp [swapCost, left, right, mismatch, runPrefix, step, swapTable, counter, one, Arithmetic.eval,
        swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc]
      rfl
    · simp [swapCost, left, right, runPrefix, step, swapTable, counter, one, Arithmetic.eval,
        swapMemory, Equiv.swap_apply_def, Function.update_comm, PMF.map_comp,
        Option.map_map, Function.comp_def, Nat.add_assoc, add_assoc, Function.update_eq_self]
      rfl

/-- The memory source returns the RAM transposition result. -/
theorem swapScan_source (count : Nat) (memory : Memory) :
    (swapScan count memory).1.registers 8 =
      applyTableSwaps count memory.ram (memory.registers 9) (memory.registers 8) := by
  induction count generalizing memory with
  | zero => rfl
  | succ count ih =>
      simp only [swapScan]
      rw [ih]
      simp [swapMemory, applyTableSwaps]

/-- The transposition scan preserves every stack and every RAM cell. -/
theorem swapScan_data (count : Nat) (memory : Memory) :
    (swapScan count memory).1.bits = memory.bits ∧ (swapScan count memory).1.ram = memory.ram := by
  induction count generalizing memory with
  | zero => simp [swapScan]
  | succ count ih => exact ih (swapMemory memory)


/-- The loop returns before its final halt and retains the exact cost. -/
theorem swapTable_loop [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) :
    runPrefix swapTable ((swapScan count memory).2 - 1) ⟨1, memory⟩ =
      PMF.pure (some (false, ⟨13, (swapScan count memory).1⟩, (swapScan count memory).2 - 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [swapScan, runPrefix, step, swapTable, counter, PMF.pure_map]
      rfl
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
        swapTable_step _ memory nonzero one,
        ih (swapMemory memory) (by omega) (by simp [swapMemory, counter, decrement])
          (by simp [swapMemory, one]), PMF.pure_map]
      rfl

/-- The entry stores the fixed increment in register fourteen. -/
def swapInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 14 1 }

/-- The full machine applies the transposition scan and counts its entry and halt. -/
theorem swapTable_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    run swapTable ((swapScan count (swapInitial memory)).2 + 1) ⟨0, memory⟩ =
      PMF.pure (some (⟨13, (swapScan count (swapInitial memory)).1⟩,
        (swapScan count (swapInitial memory)).2 + 1)) := by
  have loop := swapTable_loop count (swapInitial memory) fits
    (by simp [swapInitial, counter]) (by simp [swapInitial])
  have positive := (swapScan_cost count (swapInitial memory)).1
  have setup (fuel : Nat) : run swapTable (fuel + 1) ⟨0, memory⟩ =
      (run swapTable fuel ⟨1, swapInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
    simp [run, step, swapTable, swapInitial]
    rfl
  rw [setup]
  have remaining : (swapScan count (swapInitial memory)).2 =
      ((swapScan count (swapInitial memory)).2 - 1) + 1 := by omega
  conv_lhs => arg 2; rw [remaining, run_after_prefix, loop, PMF.pure_bind]
  simp [run, step, swapTable, PMF.pure_map]
  rw [show 1 + ((swapScan count (swapInitial memory)).2 - 1) + 1 =
    (swapScan count (swapInitial memory)).2 + 1 by omega]

/-- The machine computes the stored sparse permutation exactly. -/
theorem swapTable_source [BN254.FieldCertificate] (pairs : List (Word × Word)) (memory : Memory)
    (fits : pairs.length < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (memory.registers 9) pairs) :
    (run swapTable ((swapScan pairs.length (swapInitial memory)).2 + 1) ⟨0, memory⟩).map
      (Option.map fun result => result.1.memory.registers 8) =
      PMF.pure (some (Security.OperationalOracle.swaps pairs (memory.registers 8))) := by
  rw [swapTable_run pairs.length memory fits counter, PMF.pure_map]
  simp only [Option.map_some, swapScan_source]
  simp only [swapInitial, Function.update_of_ne (by decide : (8 : Register) ≠ 14),
    Function.update_of_ne (by decide : (9 : Register) ≠ 14)]
  rw [applyTableSwaps_source pairs memory.ram (memory.registers 9) (memory.registers 8) represented]

/-- The complete charge includes fourteen table entries and all executed instructions. -/
theorem swapTable_budget (count : Nat) (memory : Memory) :
    swapTable.size + 1 + ((swapScan count (swapInitial memory)).2 + 1) ≤ 11 * count + 17 := by
  have bound := (swapScan_cost count (swapInitial memory)).2
  change 13 + 1 + ((swapScan count (swapInitial memory)).2 + 1) ≤ _
  omega

/-- An injective representation preserves each transposition. -/
theorem encoded_swap {A : Type} [DecidableEq A] (encode : A → Word)
    (injective : Function.Injective encode) (left right value : A) :
    Equiv.swap (encode left) (encode right) (encode value) =
      encode (Equiv.swap left right value) := by
  simp only [Equiv.swap_apply_def, injective.eq_iff]
  split
  · rfl
  · split <;> rfl

/-- An injective representation preserves the complete sparse permutation. -/
theorem encoded_swaps {A : Type} [DecidableEq A] (encode : A → Word)
    (injective : Function.Injective encode) (pairs : List (A × A)) (value : A) :
    Security.OperationalOracle.swaps (pairs.map fun pair => (encode pair.1, encode pair.2))
      (encode value) = encode (Security.OperationalOracle.swaps pairs value) := by
  induction pairs generalizing value with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.map_cons, Security.OperationalOracle.swaps_cons,
        encoded_swap encode injective, ih]

/-- Canonical finite indices have an injective word representation. -/
theorem finiteWord_injective (size : Nat) (fits : size ≤ 2 ^ 256) :
    Function.Injective (fun value : Fin size => BitVec.ofNat 256 value.val) := by
  intro left right equal
  apply Fin.ext
  have values := congrArg BitVec.toNat equal
  simpa only [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_le left.isLt fits),
    Nat.mod_eq_of_lt (lt_of_lt_of_le right.isLt fits)] using values

/-- The RAM scan implements the finite-domain sparse permutation after encoding. -/
theorem applyTableSwaps_encoded {A : Type} [DecidableEq A] (encode : A → Word)
    (injective : Function.Injective encode) (pairs : List (A × A)) (ram : Word → Word)
    (address : Word) (value : A)
    (represented : RepresentsPairs ram address
      (pairs.map fun pair => (encode pair.1, encode pair.2))) :
    applyTableSwaps pairs.length ram address (encode value) =
      encode (Security.OperationalOracle.swaps pairs value) := by
  have source := applyTableSwaps_source
    (pairs.map fun pair => (encode pair.1, encode pair.2)) ram address (encode value) represented
  simpa only [List.length_map, encoded_swaps encode injective] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
