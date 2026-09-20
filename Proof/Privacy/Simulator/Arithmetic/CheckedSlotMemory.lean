import Construction.Simulator.CheckedSlot
import Proof.Privacy.Simulator.Arithmetic.HistoryAppend
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The command setup stores the exact command and selects its oracle header. -/
theorem checkedSlotStart_values (memory : Memory) :
    let result := executeLinear checkedSlotStart memory
    result.ram 26 = memory.registers 8 ∧ result.ram 27 = memory.registers 9 ∧
    result.ram 28 = memory.ram 14 ∧ result.registers 6 = oracleHeader (memory.registers 9) ∧
    result.registers 8 = memory.registers 8 ∧ result.bits = memory.bits := by
  simp [checkedSlotStart, executeLinear, LinearInstruction.execute, Arithmetic.eval, oracleHeader]

/-- The restored source keeps the saved command in a compact memory record. -/
def checkedSlotRestored (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update memory.registers 0 27) 8 (memory.ram 26)) 9 (memory.ram 27)) 10 0 }

/-- The five restore instructions implement the compact memory source. -/
theorem checkedSlotRestore_memory (memory : Memory) :
    executeLinear checkedSlotRestore memory = checkedSlotRestored memory := by
  simp [executeLinear, checkedSlotRestore, checkedSlotRestored, LinearInstruction.execute, Function.update_comm]

/-- The restore block reads the saved domain and oracle index. -/
theorem checkedSlotRestore_values (memory : Memory) :
    let result := executeLinear checkedSlotRestore memory
    result.registers 8 = memory.ram 26 ∧ result.registers 9 = memory.ram 27 ∧
    result.registers 10 = 0 ∧ result.ram = memory.ram ∧ result.bits = memory.bits := by
  simp [checkedSlotRestore, executeLinear, LinearInstruction.execute]

/-- The target block writes only the requested overlay target scratch cell. -/
theorem checkedSlotTarget_values (memory : Memory) :
    let result := executeLinear checkedSlotTarget memory
    result.ram = Function.update memory.ram 14 (memory.ram 28) ∧
    result.registers 6 = memory.registers 6 ∧ result.registers 8 = memory.registers 8 ∧
    result.bits = memory.bits := by
  simp [checkedSlotTarget, executeLinear, LinearInstruction.execute]

/-- The history setup reads the saved requested pair. -/
theorem checkedSlotHistory_values (memory : Memory) :
    let result := executeLinear checkedSlotHistory memory
    result.registers 8 = memory.ram 26 ∧ result.registers 10 = memory.ram 28 ∧
    result.ram = memory.ram ∧ result.bits = memory.bits := by
  simp [checkedSlotHistory, executeLinear, LinearInstruction.execute]

/-- A collision changes only the persistent bad flag in RAM. -/
theorem checkedSlotCollision_ram (memory : Memory) :
    (executeLinear checkedSlotCollision memory).ram = Function.update memory.ram 31 1 := by
  simp [checkedSlotCollision, executeLinear, LinearInstruction.execute]

/-- The final source appends the permutation override and its requested history pair. -/
def checkedSlotFinished (memory : Memory) : Memory :=
  historyAppended (executeLinear checkedSlotHistory
    (overlayAppended (executeLinear checkedSlotTarget memory)))

/-- The successful finish charges forty fixed instructions. -/
def checkedSlotFinish : List LinearInstruction :=
  checkedSlotTarget ++ overlayAppend ++ checkedSlotHistory ++ historyAppend

theorem checkedSlotFinish_length : checkedSlotFinish.length = 40 := rfl

theorem checkedSlotFinish_memory (memory : Memory) :
    executeLinear checkedSlotFinish memory = checkedSlotFinished memory := by
  simp only [checkedSlotFinish, executeLinear_append, overlayAppend_memory, historyAppend_memory, checkedSlotFinished]

/-- The fixed command blocks have their exact instruction lengths. -/
theorem checkedSlotLengths : checkedSlotStart.length = 12 ∧ checkedSlotRestore.length = 5 ∧
    checkedSlotTarget.length = 4 ∧ checkedSlotHistory.length = 4 ∧ checkedSlotCollision.length = 3 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
