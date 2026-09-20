import Construction.Simulator.HistoryFresh
import Proof.Privacy.Simulator.Arithmetic.TableBlock
import Proof.Privacy.Simulator.Arithmetic.HistoryAppend

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The domain loader reads the history pointer and count. -/
def historyDomainReady (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update memory.registers
    9 (historyHeader memory + 256#256)) 10 (memory.ram (historyHeader memory))) 14 256 }

/-- The range loader reads the saved requested range. -/
def historyRangeReady (memory : Memory) : Memory :=
  let registers := Function.update memory.registers 9 (historyHeader memory + 257#256)
  let registers := Function.update registers 10 (memory.ram (historyHeader memory))
  let registers := Function.update registers 14 257
  let registers := Function.update registers 15 14
  { memory with registers := Function.update registers 8 (memory.ram 14) }

theorem historyDomainLoad_memory (memory : Memory) :
    executeLinear historyDomainLoad memory = historyDomainReady memory := by
  simp [historyDomainLoad, historyDomainReady, historyHeader, executeLinear,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

theorem historyRangeLoad_memory (memory : Memory) :
    executeLinear historyRangeLoad memory = historyRangeReady memory := by
  simp [historyRangeLoad, historyRangeReady, historyHeader, executeLinear,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The domain source retains the exact lookup state and cost. -/
def historyDomainScan (count : Nat) (memory : Memory) : Memory × Nat :=
  tableScan count (tableInitial (historyDomainReady memory))

/-- The range source retains the exact lookup state and cost. -/
def historyRangeScan (count : Nat) (memory : Memory) : Memory × Nat :=
  tableScan count (tableInitial (historyRangeReady memory))

/-- The freshness source rejects a domain collision before it scans ranges. -/
def historyFreshSource (count : Nat) (memory : Memory) : Memory × Nat :=
  let domain := historyDomainScan count memory
  if domain.1.registers 12 = 0 then
    let range := historyRangeScan count domain.1
    ({range.1 with registers := Function.update range.1.registers 7 (range.1.registers 12 ^^^ 1)},
      domain.2 + range.2 + 17)
  else ({domain.1 with registers := Function.update domain.1.registers 7 0}, domain.2 + 8)

/-- A table scan leaves every register below nine unchanged. -/
theorem tableScan_low (count : Nat) (memory : Memory) (register : Register) (low : register.val < 9) :
    (tableScan count memory).1.registers register = memory.registers register := by
  have different (target : Register) (high : 9 ≤ target.val) : register ≠ target := by
    intro same; have vals := congrArg Fin.val same; omega
  induction count generalizing memory with
  | zero => simp [tableScan, Function.update_of_ne (different 12 (by decide))]
  | succ count ih =>
    simp only [tableScan]
    split
    · simp [tableMatch, tableCompare, Function.update_of_ne (different 9 (by decide)),
        Function.update_of_ne (different 11 (by decide)), Function.update_of_ne (different 12 (by decide)),
        Function.update_of_ne (different 13 (by decide))]
    · rw [ih]
      simp [tableMiss, tableCompare, Function.update_of_ne (different 9 (by decide)),
        Function.update_of_ne (different 10 (by decide)), Function.update_of_ne (different 13 (by decide))]

/-- The lookup flag is always a canonical Boolean word. -/
theorem tableScan_flag (count : Nat) (memory : Memory) :
    (tableScan count memory).1.registers 12 = 0 ∨ (tableScan count memory).1.registers 12 = 1 := by
  induction count generalizing memory with
  | zero => simp [tableScan]
  | succ count ih =>
    simp only [tableScan]
    split
    · simp [tableMatch]
    · exact ih _

/-- The freshness source has a linear bound in the history length. -/
theorem historyFreshSource_cost (count : Nat) (memory : Memory) :
    (historyFreshSource count memory).2 ≤ 12 * count + 23 := by
  have first := tableScan_cost count (tableInitial (historyDomainReady memory))
  have second := tableScan_cost count
    (tableInitial (historyRangeReady (historyDomainScan count memory).1))
  unfold historyFreshSource
  dsimp only
  split <;> dsimp only
  · change (historyDomainScan count memory).2 +
      (historyRangeScan count (historyDomainScan count memory).1).2 + 17 ≤ _
    dsimp only [historyDomainScan, historyRangeScan] at *
    omega
  · dsimp only [historyDomainScan] at *
    omega

/-- The domain scan preserves the history header, RAM, and bit stacks. -/
theorem historyDomainScan_data (count : Nat) (memory : Memory) :
    (historyDomainScan count memory).1.ram = memory.ram ∧
    (historyDomainScan count memory).1.bits = memory.bits ∧
    (historyDomainScan count memory).1.registers 6 = memory.registers 6 := by
  have data := tableScan_data count (tableInitial (historyDomainReady memory))
  have header := tableScan_low count (tableInitial (historyDomainReady memory)) 6 (by decide)
  constructor
  · exact data.2
  constructor
  · exact data.1
  · exact header

/-- The selected tail sets the acceptance flag and charges all remaining instructions. -/
def historyFreshTail (count : Nat) (memory : Memory) : Memory × Nat :=
  if memory.registers 12 = 0 then
    let range := historyRangeScan count memory
    ({range.1 with registers := Function.update range.1.registers 7 (range.1.registers 12 ^^^ 1)},
      range.2 + 11)
  else ({memory with registers := Function.update memory.registers 7 0}, 2)

/-- The complete source joins the domain scan and its selected tail. -/
theorem historyFreshSource_tail (count : Nat) (memory : Memory) :
    historyFreshSource count memory =
      ((historyFreshTail count (historyDomainScan count memory).1).1,
        (historyDomainScan count memory).2 + 6 + (historyFreshTail count (historyDomainScan count memory).1).2) := by
  simp only [historyFreshSource, historyFreshTail]
  split <;> simp only [Prod.mk.injEq, true_and] <;> omega

/-- The freshness scan preserves RAM, bit stacks, and the oracle header. -/
theorem historyFreshSource_data (count : Nat) (memory : Memory) :
    (historyFreshSource count memory).1.ram = memory.ram ∧
    (historyFreshSource count memory).1.bits = memory.bits ∧
    (historyFreshSource count memory).1.registers 6 = memory.registers 6 := by
  have domain := historyDomainScan_data count memory
  have range := tableScan_data count (tableInitial (historyRangeReady (historyDomainScan count memory).1))
  have header := tableScan_low count (tableInitial (historyRangeReady (historyDomainScan count memory).1)) 6 (by decide)
  change (historyRangeScan count (historyDomainScan count memory).1).1.registers 6 =
    (historyDomainScan count memory).1.registers 6 at header
  simp only [historyFreshSource]
  split
  · refine ⟨range.2.trans domain.1, range.1.trans domain.2.1, ?_⟩
    change (historyRangeScan count (historyDomainScan count memory).1).1.registers 6 = _
    exact header.trans domain.2.2
  · refine ⟨domain.1, domain.2.1, ?_⟩
    exact domain.2.2

end Kriterion.ArgoMAC.ArithmeticSimulator
