import Construction.Simulator.TableLookup

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The comparison stores the current key difference. -/
def tableCompare (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 13 (memory.ram (memory.registers 9) ^^^ memory.registers 8) }

/-- A missed entry advances the address and reduces the remaining count. -/
def tableMiss (memory : Memory) : Memory :=
  { tableCompare memory with registers := Function.update (Function.update (tableCompare memory).registers 9 (memory.registers 9 + 2)) 10 (memory.registers 10 - 1) }

/-- A matching entry returns its stored value. -/
def tableMatch (memory : Memory) : Memory :=
  { tableCompare memory with registers := Function.update (Function.update (Function.update (tableCompare memory).registers 9 (memory.registers 9 + 1)) 11 (memory.ram (memory.registers 9 + 1))) 12 1 }

/-- The source retains every memory effect and actual instruction count. -/
def tableScan : Nat → Memory → Memory × Nat
  | 0, memory => ({ memory with registers := Function.update memory.registers 12 0 }, 3)
  | count + 1, memory =>
      if memory.ram (memory.registers 9) = memory.registers 8 then (tableMatch memory, 8)
      else let result := tableScan count (tableMiss memory)
           (result.1, result.2 + 6)

/-- A positive bounded count has a nonzero word representation. -/
private theorem tableCount_nonzero (count : Nat) (fits : count + 1 < 2 ^ 256) :
    BitVec.ofNat 256 (count + 1) ≠ 0#256 := by
  intro equal
  have values := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at values
  change count + 1 = 0 at values
  omega

/-- A missed entry uses six instructions before the next iteration. -/
theorem tableLookup_miss [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256)
    (one : memory.registers 14 = 1#256) (two : memory.registers 15 = 2#256)
    (different : memory.ram (memory.registers 9) ≠ memory.registers 8) :
    run tableLookup (fuel + 6) ⟨2, memory⟩ =
      (run tableLookup fuel ⟨2, tableMiss memory⟩).map
        (Option.map fun result => (result.1, result.2 + 6)) := by
  have comparison : memory.ram (memory.registers 9) ^^^ memory.registers 8 ≠ 0#256 := by
    simpa using different
  simp [run, step, tableLookup, counter, one, two, comparison, Arithmetic.eval,
    tableMiss, tableCompare, Function.update_comm, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc]
  rfl

/-- A matching entry uses eight instructions and returns the stored value. -/
theorem tableLookup_match [BN254.FieldCertificate] (fuel : Nat) (memory : Memory)
    (counter : memory.registers 10 ≠ 0#256) (one : memory.registers 14 = 1#256)
    (matched : memory.ram (memory.registers 9) = memory.registers 8) :
    run tableLookup (fuel + 8) ⟨2, memory⟩ =
      PMF.pure (some (⟨9, tableMatch memory⟩, 8)) := by
  simp [run, step, tableLookup, counter, one, matched, Arithmetic.eval,
    tableMatch, tableCompare, Function.update_comm, PMF.pure_map]
  rfl

/-- The machine loop implements the first-match table source and exact cost. -/
theorem tableLookup_loop [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) (two : memory.registers 15 = 2#256) :
    run tableLookup (6 * count + 3) ⟨2, memory⟩ =
      PMF.pure (some (⟨9, (tableScan count memory).1⟩, (tableScan count memory).2)) := by
  induction count generalizing memory with
  | zero =>
      simp [run, step, tableLookup, counter, tableScan, PMF.pure_map]
      rfl
  | succ count ih =>
      have decrement : BitVec.ofNat 256 (count + 1) - 1#256 = BitVec.ofNat 256 count := by
        rw [BitVec.ofNat_add]
        simp
      have nonzero : memory.registers 10 ≠ 0#256 := by
        rw [counter]
        exact tableCount_nonzero count fits
      by_cases matched : memory.ram (memory.registers 9) = memory.registers 8
      · rw [show 6 * (count + 1) + 3 = (6 * count + 1) + 8 by omega,
          tableLookup_match _ memory nonzero one matched]
        simp [tableScan, matched]
      · rw [show 6 * (count + 1) + 3 = (6 * count + 3) + 6 by omega,
          tableLookup_miss _ memory nonzero one two matched]
        rw [ih (tableMiss memory) (by omega)
          (by simp [tableMiss, counter, decrement])
          (by simp [tableMiss, tableCompare, one])
          (by simp [tableMiss, tableCompare, two])]
        simp [tableScan, matched, PMF.pure_map]

/-- The result flag distinguishes a missing key from every possible stored value. -/
def tableResult (memory : Memory) : Option Word :=
  if memory.registers 12 = 0 then none else some (memory.registers 11)

/-- The memory-level source agrees with the first-match table lookup. -/
theorem tableScan_source (count : Nat) (memory : Memory) :
    tableResult (tableScan count memory).1 =
      findTable count memory.ram (memory.registers 9) (memory.registers 8) := by
  induction count generalizing memory with
  | zero => simp [tableScan, tableResult, findTable]
  | succ count ih =>
      simp only [tableScan, findTable]
      split
      · simp [tableResult, tableMatch, tableCompare]
      · rw [ih]
        simp [tableMiss, tableCompare]

/-- The table scan preserves every stack and every RAM cell. -/
theorem tableScan_data (count : Nat) (memory : Memory) :
    (tableScan count memory).1.bits = memory.bits ∧
      (tableScan count memory).1.ram = memory.ram := by
  induction count generalizing memory with
  | zero => simp [tableScan]
  | succ count ih =>
      simp only [tableScan]
      split
      · simp [tableMatch, tableCompare]
      · exact ih (tableMiss memory)

/-- The table loop executes at most six instructions per entry and three final instructions. -/
theorem tableScan_cost (count : Nat) (memory : Memory) :
    (tableScan count memory).2 ≤ 6 * count + 3 := by
  induction count generalizing memory with
  | zero => simp [tableScan]
  | succ count ih =>
      simp only [tableScan]
      split
      · simp; omega
      · have bound := ih (tableMiss memory)
        dsimp only at bound ⊢
        omega

/-- The entry block initializes the two constant registers. -/
def tableInitial (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update memory.registers 14 1) 15 2 }

/-- The complete table machine retains the exact scan cost. -/
theorem tableLookup_run [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    run tableLookup (6 * count + 5) ⟨0, memory⟩ =
      PMF.pure (some (⟨9, (tableScan count (tableInitial memory)).1⟩,
        (tableScan count (tableInitial memory)).2 + 2)) := by
  have setup (fuel : Nat) : run tableLookup (fuel + 2) ⟨0, memory⟩ =
      (run tableLookup fuel ⟨2, tableInitial memory⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
    simp [run, step, tableLookup, tableInitial, PMF.map_comp, Option.map_map,
      Function.comp_def, Nat.add_assoc]
    rfl
  rw [show 6 * count + 5 = (6 * count + 3) + 2 by omega, setup,
    tableLookup_loop count (tableInitial memory) fits (by simp [tableInitial, counter])
      (by simp [tableInitial]) (by simp [tableInitial]), PMF.pure_map]
  rfl

/-- The machine returns the first matching RAM value, including values equal to zero. -/
theorem tableLookup_source [BN254.FieldCertificate] (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    (run tableLookup (6 * count + 5) ⟨0, memory⟩).map
      (Option.map fun result => tableResult result.1.memory) =
      PMF.pure (some (findTable count memory.ram (memory.registers 9) (memory.registers 8))) := by
  rw [tableLookup_run count memory fits counter, PMF.pure_map]
  simp [tableScan_source, tableInitial]

/-- The table and execution together cost at most six units per entry plus eighteen. -/
theorem tableLookup_budget (count : Nat) (memory : Memory) :
    tableLookup.size + 1 + ((tableScan count (tableInitial memory)).2 + 2) ≤
      6 * count + 18 := by
  have bound := tableScan_cost count (tableInitial memory)
  change 12 + 1 + ((tableScan count (tableInitial memory)).2 + 2) ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
