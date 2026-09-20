import Proof.Privacy.Simulator.Arithmetic.PublicHistoryRun
import Proof.Privacy.Simulator.Arithmetic.DescendingPairsLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The append source changes exactly two pair cells and their count header. -/
theorem historyAppended_ram (memory : Memory) :
    (historyAppended memory).ram =
      Function.update
        (Function.update
          (Function.update memory.ram
            (historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256))
            (memory.registers 8))
          (historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) + 1#256)
          (memory.registers 10))
        (historyHeader memory) (memory.ram (historyHeader memory) + 1#256) := by
  simp [historyAppended, overlayAppendFinished, pairStored, historyAppendReady]

/-- The result writes the visible pair only for accepted external fixed-key queries. -/
theorem publicHistoryResult_ram (memory : Memory) (headerSafe : historyHeader memory ≠ 50#256) :
    (publicHistoryResult memory).1.ram =
      if memory.registers 7 = 0#256 then memory.ram
      else if memory.ram 49#256 = 0#256 ∨ memory.ram 49#256 = 1#256 then
        Function.update
          (Function.update
            (Function.update (Function.update memory.ram 50 (memory.registers 8))
              (historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256))
              (if memory.ram 49#256 = 0#256 then memory.ram 48 else memory.registers 8))
            (historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) + 1#256)
            (if memory.ram 49#256 = 0#256 then memory.registers 8 else memory.ram 48))
          (historyHeader memory) (memory.ram (historyHeader memory) + 1#256)
      else memory.ram := by
  unfold publicHistoryResult
  split
  · rfl
  · split
    · rename_i accepted forward
      simp only [publicHistoryFinished, (publicHistoryRestore_state _).2.1, historyAppended_ram]
      simp [publicHistoryForwardReady, publicHistoryForward, executeLinear, LinearInstruction.execute,
        Arithmetic.eval, historyHeader, forward, accepted, headerSafe, historyHeader] at *
      all_goals simp_all [Function.update_of_ne, ne_comm]
    · rename_i accepted notForward
      split
      · rename_i inverse
        simp only [publicHistoryFinished, (publicHistoryRestore_state _).2.1, historyAppended_ram]
        simp [publicHistoryInverseReady, publicHistoryForwardReady, publicHistoryInverse, executeLinear,
          LinearInstruction.execute, historyHeader, notForward, inverse, accepted, headerSafe, historyHeader] at *
        all_goals simp_all [Function.update_of_ne, ne_comm]
      · rename_i notInverse
        simp [publicHistoryInverseReady, publicHistoryForwardReady, accepted, notForward, notInverse]

/-- The result retains the answer when the public history cannot overlap its saved reply. -/
theorem publicHistoryResult_reply (memory : Memory)
    (headerSafe : historyHeader memory ≠ 50#256)
    (domainSafe : historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) ≠ 50#256)
    (rangeSafe : historyHeader memory + (memory.ram (historyHeader memory) * 2#256 + 256#256) + 1#256 ≠ 50#256) :
    (publicHistoryResult memory).1.registers 8 = memory.registers 8 := by
  unfold publicHistoryResult
  split
  · rfl
  · split
    · simp only [publicHistoryFinished, (publicHistoryRestore_state _).1, historyAppended_ram]
      simp [publicHistoryForwardReady, publicHistoryForward, executeLinear, LinearInstruction.execute,
        Arithmetic.eval, historyHeader, headerSafe, Ne.symm headerSafe, Ne.symm domainSafe, Ne.symm rangeSafe,
        historyHeader] at *
      all_goals simp_all [Function.update_of_ne, ne_comm]
    · split
      · simp only [publicHistoryFinished, (publicHistoryRestore_state _).1, historyAppended_ram]
        simp [publicHistoryInverseReady, publicHistoryForwardReady, publicHistoryInverse, executeLinear,
          LinearInstruction.execute, historyHeader, headerSafe, Ne.symm headerSafe, Ne.symm domainSafe,
          Ne.symm rangeSafe, historyHeader] at *
        all_goals simp_all [Function.update_of_ne, ne_comm]
      · rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
