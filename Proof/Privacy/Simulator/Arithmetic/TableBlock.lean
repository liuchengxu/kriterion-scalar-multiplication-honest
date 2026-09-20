import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.Blocks
import Proof.Privacy.Simulator.Arithmetic.TableLookup

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the table lookup and supplies its own return instruction. -/
def ContainsTableLookup (host : Machine) (labels : Fin 13 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 13, pc ≠ 9 → host.code[(labels pc).val] =
    relocate labels (tableLookup.code[pc.val]'(by exact pc.isLt))

/-- A missed entry costs six instructions in the host. -/
theorem tableBlock_miss [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (fuel : Nat) (memory : Memory) (counter : memory.registers 10 ≠ 0#256)
    (one : memory.registers 14 = 1#256) (two : memory.registers 15 = 2#256)
    (different : memory.ram (memory.registers 9) ≠ memory.registers 8) :
    runPrefix host (fuel + 6) ⟨labels 2, memory⟩ =
      (runPrefix host fuel ⟨labels 2, tableMiss memory⟩).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 6)) := by
  have comparison : memory.ram (memory.registers 9) ^^^ memory.registers 8 ≠ 0#256 := by
    simpa using different
  simp [runPrefix, step, present 2 (by decide), present 3 (by decide),
    present 4 (by decide), present 5 (by decide), present 6 (by decide), present 7 (by decide),
    tableLookup, relocate, counter, one, two, comparison, Arithmetic.eval,
    tableMiss, tableCompare, Function.update_comm, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc]

/-- A matching entry returns before the host executes its continuation. -/
theorem tableBlock_match [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (memory : Memory) (counter : memory.registers 10 ≠ 0#256)
    (one : memory.registers 14 = 1#256)
    (matched : memory.ram (memory.registers 9) = memory.registers 8) :
    runPrefix host 7 ⟨labels 2, memory⟩ =
      PMF.pure (some (false, ⟨labels 9, tableMatch memory⟩, 7)) := by
  simp [runPrefix, step, present 2 (by decide), present 3 (by decide),
    present 4 (by decide), present 5 (by decide), present 10 (by decide),
    present 11 (by decide), present 12 (by decide), tableLookup, relocate,
    counter, one, matched, Arithmetic.eval, tableMatch, tableCompare,
    Function.update_comm, PMF.pure_map]

/-- Every table scan includes its final halt charge. -/
theorem tableScan_positive (count : Nat) (memory : Memory) :
    1 ≤ (tableScan count memory).2 := by
  cases count with
  | zero => simp [tableScan]
  | succ count => simp only [tableScan]; split <;> simp

/-- The host executes exactly the required scan prefix. -/
theorem tableBlock_loop [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count)
    (one : memory.registers 14 = 1#256) (two : memory.registers 15 = 2#256) :
    runPrefix host ((tableScan count memory).2 - 1) ⟨labels 2, memory⟩ =
      PMF.pure (some (false, ⟨labels 9, (tableScan count memory).1⟩,
        (tableScan count memory).2 - 1)) := by
  induction count generalizing memory with
  | zero =>
      simp [tableScan, runPrefix, step, present 2 (by decide), present 8 (by decide),
        tableLookup, relocate, counter, PMF.pure_map]
  | succ count ih =>
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
      by_cases matched : memory.ram (memory.registers 9) = memory.registers 8
      · simpa [tableScan, matched] using tableBlock_match host labels present memory nonzero one matched
      · have positive := tableScan_positive count (tableMiss memory)
        simp only [tableScan, if_neg matched]
        rw [show (tableScan count (tableMiss memory)).2 + 6 - 1 =
          ((tableScan count (tableMiss memory)).2 - 1) + 6 by omega]
        rw [tableBlock_miss host labels present _ memory nonzero one two matched]
        rw [ih (tableMiss memory) (by omega)
          (by simp [tableMiss, counter, decrement])
          (by simp [tableMiss, tableCompare, one])
          (by simp [tableMiss, tableCompare, two]), PMF.pure_map]
        rfl

/-- The host initializes the constant registers in two instructions. -/
theorem tableBlock_setup [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (memory : Memory) :
    runPrefix host 2 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 2, tableInitial memory⟩, 2)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide),
    tableLookup, relocate, tableInitial, PMF.pure_map]

/-- The full table block returns its complete memory and exact prefix cost. -/
theorem tableBlock_prefix [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) :
    runPrefix host ((tableScan count (tableInitial memory)).2 + 1) ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 9, (tableScan count (tableInitial memory)).1⟩,
        (tableScan count (tableInitial memory)).2 + 1)) := by
  have positive := tableScan_positive count (tableInitial memory)
  rw [show (tableScan count (tableInitial memory)).2 + 1 =
    2 + ((tableScan count (tableInitial memory)).2 - 1) by omega,
    prefix_add, tableBlock_setup host labels present memory, PMF.pure_bind]
  dsimp only
  rw [tableBlock_loop host labels present count (tableInitial memory) fits
      (by simp [tableInitial, counter]) (by simp [tableInitial]) (by simp [tableInitial]),
    PMF.pure_map]
  simp [Nat.add_comm]

/-- The lookup passes its state and exact charge to the host continuation. -/
theorem tableBlock_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 13 → Fin (host.size + 1)) (present : ContainsTableLookup host labels)
    (count : Nat) (memory : Memory) (fits : count < 2 ^ 256)
    (counter : memory.registers 10 = BitVec.ofNat 256 count) (fuel : Nat) :
    run host ((tableScan count (tableInitial memory)).2 + 1 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 9, (tableScan count (tableInitial memory)).1⟩).map
        (Option.map fun result => (result.1, result.2 + ((tableScan count (tableInitial memory)).2 + 1))) := by
  rw [run_after_prefix, tableBlock_prefix host labels present count memory fits counter,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
