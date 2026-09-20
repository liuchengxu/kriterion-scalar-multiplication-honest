import Construction.Simulator.HistoryAppend
import Proof.Privacy.Simulator.Arithmetic.OverlayPairs

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The setup instructions implement the history cursor exactly. -/
theorem historyAppendSetup_memory (memory : Memory) :
    executeLinear historyAppendSetup memory = historyAppendReady memory := by
  simp [executeLinear, historyAppendSetup, historyAppendReady, historyHeader,
    LinearInstruction.execute, Arithmetic.eval, Function.update_comm]

/-- The append instructions implement the history source exactly. -/
theorem historyAppend_memory (memory : Memory) : executeLinear historyAppend memory = historyAppended memory := by
  simp only [historyAppend, executeLinear_append, historyAppendSetup_memory, pairStore_memory,
    overlayAppendFinish_memory, historyAppended]

/-- The append block preserves the domain, range, header, acceptance flag, and stacks. -/
theorem historyAppended_data (memory : Memory) :
    (historyAppended memory).registers 8 = memory.registers 8 ∧
    (historyAppended memory).registers 10 = memory.registers 10 ∧
    (historyAppended memory).registers 6 = memory.registers 6 ∧
    (historyAppended memory).registers 7 = memory.registers 7 ∧
    (historyAppended memory).bits = memory.bits := by
  simp [historyAppended, overlayAppendFinished, pairStored, historyAppendReady]

/-- The host returns after all fifteen history append instructions. -/
theorem historyAppend_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host historyAppend labels)
    (memory : Memory) (fuel : Nat) :
    run host (15 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 15, historyAppended memory⟩).map
        (Option.map fun result => (result.1, result.2 + 15)) := by
  simpa only [historyAppend_memory, show historyAppend.length = 15 from rfl] using
    linear_continue host historyAppend labels present memory fuel

/-- The history cursor points to the first unused pair. -/
theorem historyAppendReady_cursor (memory : Memory) (pairs : List (Word × Word))
    (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 pairs.length) :
    (historyAppendReady memory).registers 9 =
      historyHeader memory + 256#256 + BitVec.ofNat 256 (2 * pairs.length) := by
  simp [historyAppendReady, counter, ← BitVec.ofNat_mul, Nat.mul_comm,
    add_assoc, add_comm, add_left_comm]

/-- The appended RAM contains the exact ordered pair history. -/
theorem historyAppended_represents (memory : Memory) (pairs : List (Word × Word))
    (counter : memory.ram (historyHeader memory) = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (historyHeader memory + 256#256) pairs)
    (fits : 2 * pairs.length + 2 ≤ 2 ^ 256)
    (headerSafe : ∀ index, index < 2 * (pairs.length + 1) →
      historyHeader memory + 256#256 + BitVec.ofNat 256 index ≠ historyHeader memory) :
    RepresentsPairs (historyAppended memory).ram (historyHeader memory + 256#256)
      (pairs ++ [(memory.registers 8, memory.registers 10)]) := by
  have stored := pairStored_appends (historyAppendReady memory) pairs
    (historyHeader memory + 256#256) (historyAppendReady_cursor memory pairs counter) represented fits
  have values : (historyAppendReady memory).registers 8 = memory.registers 8 ∧
      (historyAppendReady memory).registers 10 = memory.registers 10 := by simp [historyAppendReady]
  rw [values.1, values.2] at stored
  apply RepresentsPairs.congr _ _ _ _ stored
  intro index bound
  have safe := headerSafe index (by simpa using bound)
  simp [historyAppended, overlayAppendFinished, pairStored, historyAppendReady, safe]

/-- The append block increases the history count by one. -/
theorem historyAppended_count (memory : Memory) :
    (historyAppended memory).ram (historyHeader memory) = memory.ram (historyHeader memory) + 1#256 := by
  simp [historyAppended, overlayAppendFinished, pairStored, historyAppendReady]

end Kriterion.ArgoMAC.ArithmeticSimulator
