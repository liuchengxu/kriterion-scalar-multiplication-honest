import Proof.Privacy.Simulator.Arithmetic.HistoryFreshMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A zero lookup flag is exactly a missing table key. -/
theorem tableScan_missing (count : Nat) (memory : Memory) :
    (tableScan count memory).1.registers 12 = 0 ↔
      findTable count memory.ram (memory.registers 9) (memory.registers 8) = none := by
  rw [← tableScan_source]
  simp only [tableResult]
  split <;> simp_all

/-- The domain scan rejects exactly the recorded domains. -/
theorem findTable_domains_none (ram : Word → Word) (address key : Word) (pairs : List (Word × Word))
    (stored : RepresentsPairs ram address pairs) :
    findTable pairs.length ram address key = none ↔ ∀ pair ∈ pairs, pair.1 ≠ key := by
  induction pairs generalizing address with
  | nil => simp [findTable]
  | cons pair tail ih =>
    rcases stored with ⟨left, right, rest⟩
    simp only [List.length_cons, findTable, left]
    by_cases same : pair.1 = key
    · simp [same]
    · rw [if_neg same, ih (address + 2) rest]
      rw [List.forall_mem_cons]
      exact ⟨fun rest => ⟨same, rest⟩, fun all => all.2⟩

/-- The range scan rejects exactly the recorded ranges. -/
theorem findTable_ranges_none (ram : Word → Word) (address key : Word) (pairs : List (Word × Word))
    (stored : RepresentsPairs ram address pairs) :
    findTable pairs.length ram (address + 1) key = none ↔ ∀ pair ∈ pairs, pair.2 ≠ key := by
  induction pairs generalizing address with
  | nil => simp [findTable]
  | cons pair tail ih =>
    rcases stored with ⟨left, right, rest⟩
    simp only [List.length_cons, findTable]
    change ram (address + 1) = pair.2 at right
    rw [right]
    by_cases same : pair.2 = key
    · simp [same]
    · have next : address + 1 + 2 = address + 2 + 1 := by ac_rfl
      simp only [if_neg same, next]
      rw [ih (address + 2) rest]
      rw [List.forall_mem_cons]
      exact ⟨fun rest => ⟨same, rest⟩, fun all => all.2⟩

/-- The domain scan's zero flag means that the requested domain is fresh. -/
theorem historyDomainScan_missing (pairs : List (Word × Word)) (memory : Memory)
    (stored : RepresentsPairs memory.ram (historyHeader memory + 256#256) pairs) :
    (historyDomainScan pairs.length memory).1.registers 12 = 0 ↔
      ∀ pair ∈ pairs, pair.1 ≠ memory.registers 8 := by
  rw [historyDomainScan, tableScan_missing]
  change findTable pairs.length memory.ram (historyHeader memory + 256#256) (memory.registers 8) = none ↔ _
  exact findTable_domains_none _ _ _ pairs stored

/-- The range scan's zero flag means that the requested range is fresh. -/
theorem historyRangeScan_missing (pairs : List (Word × Word)) (memory : Memory)
    (stored : RepresentsPairs memory.ram (historyHeader memory + 256#256) pairs) :
    (historyRangeScan pairs.length memory).1.registers 12 = 0 ↔
      ∀ pair ∈ pairs, pair.2 ≠ memory.ram 14 := by
  rw [historyRangeScan, tableScan_missing]
  change findTable pairs.length memory.ram (historyHeader memory + 257#256) (memory.ram 14) = none ↔ _
  have offset : historyHeader memory + 257#256 = historyHeader memory + 256#256 + 1 := by
    rw [add_assoc]
    rfl
  rw [offset]
  exact findTable_ranges_none _ _ _ pairs stored

/-- The accepted flag is exactly simultaneous domain and range freshness. -/
theorem historyFreshSource_accepts (pairs : List (Word × Word)) (memory : Memory)
    (stored : RepresentsPairs memory.ram (historyHeader memory + 256#256) pairs) :
    (historyFreshSource pairs.length memory).1.registers 7 = 1 ↔
      (∀ pair ∈ pairs, pair.1 ≠ memory.registers 8) ∧ (∀ pair ∈ pairs, pair.2 ≠ memory.ram 14) := by
  have saved := historyDomainScan_data pairs.length memory
  have retained : RepresentsPairs (historyDomainScan pairs.length memory).1.ram
      (historyHeader (historyDomainScan pairs.length memory).1 + 256#256) pairs := by
    simpa only [historyHeader, saved.1, saved.2.2] using stored
  have domain := historyDomainScan_missing pairs memory stored
  have range := historyRangeScan_missing pairs (historyDomainScan pairs.length memory).1 retained
  rw [saved.1] at range
  have flag := tableScan_flag pairs.length
    (tableInitial (historyRangeReady (historyDomainScan pairs.length memory).1))
  change (historyRangeScan pairs.length (historyDomainScan pairs.length memory).1).1.registers 12 = 0 ∨
    (historyRangeScan pairs.length (historyDomainScan pairs.length memory).1).1.registers 12 = 1 at flag
  simp only [historyFreshSource]
  split
  · rename_i fresh
    have domainFresh := domain.mp fresh
    rcases flag with missing | found
    · change ((historyRangeScan pairs.length (historyDomainScan pairs.length memory).1).1.registers 12 ^^^ 1) = 1 ↔ _
      rw [missing]
      constructor
      · intro _; exact ⟨domainFresh, range.mp missing⟩
      · intro _; decide
    · change ((historyRangeScan pairs.length (historyDomainScan pairs.length memory).1).1.registers 12 ^^^ 1) = 1 ↔ _
      rw [found]
      constructor
      · intro impossible
        exact False.elim ((by decide : ¬ ((1 : Word) ^^^ 1) = 1) impossible)
      · intro freshPair
        have absent := range.mpr freshPair.2
        rw [found] at absent
        exact False.elim ((by decide : (1 : Word) ≠ 0) absent)
  · rename_i collision
    change (0 : Word) = 1 ↔ _
    constructor
    · intro impossible
      exact False.elim ((by decide : (0 : Word) ≠ 1) impossible)
    · intro freshPair
      exact False.elim (collision (domain.mpr freshPair.1))

end Kriterion.ArgoMAC.ArithmeticSimulator
