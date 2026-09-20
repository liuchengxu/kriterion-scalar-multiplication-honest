import Construction.Simulator.PublicHistory
import Proof.Privacy.Simulator.Arithmetic.HistoryAppend

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block preserves the query registers and writes only two scratch cells. -/
theorem publicHistorySave_state (memory : Memory) :
    let final := executeLinear publicHistorySave memory
    final.ram = Function.update (Function.update memory.ram 48 (memory.registers 8))
      49 (memory.registers 10) ∧ final.bits = memory.bits ∧
    final.registers 8 = memory.registers 8 ∧ final.registers 9 = memory.registers 9 ∧
    final.registers 10 = memory.registers 10 := by
  simp [executeLinear, publicHistorySave, LinearInstruction.execute]

/-- The forward setup gives the appender the actual visible query pair. -/
theorem publicHistoryForward_state (memory : Memory) :
    let final := executeLinear publicHistoryForward memory
    final.registers 8 = memory.ram 48 ∧ final.registers 10 = memory.registers 8 ∧
    final.registers 6 = memory.registers 6 ∧ final.registers 7 = memory.registers 7 ∧
    final.ram = Function.update memory.ram 50 (memory.registers 8) ∧ final.bits = memory.bits := by
  simp [executeLinear, publicHistoryForward, LinearInstruction.execute, Arithmetic.eval]

/-- The inverse setup gives the appender the actual visible query pair. -/
theorem publicHistoryInverse_state (memory : Memory) :
    let final := executeLinear publicHistoryInverse memory
    final.registers 8 = memory.registers 8 ∧ final.registers 10 = memory.ram 48 ∧
    final.registers 6 = memory.registers 6 ∧ final.registers 7 = memory.registers 7 ∧
    final.ram = Function.update memory.ram 50 (memory.registers 8) ∧ final.bits = memory.bits := by
  simp [executeLinear, publicHistoryInverse, LinearInstruction.execute]

/-- The restore block returns the oracle reply and preserves all stored data. -/
theorem publicHistoryRestore_state (memory : Memory) :
    let final := executeLinear publicHistoryRestore memory
    final.registers 8 = memory.ram 50 ∧ final.ram = memory.ram ∧ final.bits = memory.bits := by
  simp [executeLinear, publicHistoryRestore, LinearInstruction.execute]

/-- Each fixed history block has its exact instruction length. -/
theorem publicHistory_lengths :
    publicHistorySave.length = 4 ∧ publicHistoryForward.length = 6 ∧
    publicHistoryInverse.length = 4 ∧ publicHistoryRestore.length = 2 := by decide

end Kriterion.ArgoMAC.ArithmeticSimulator
