import Proof.Privacy.Simulator.Arithmetic.EncLinkCount
import Proof.Privacy.Simulator.Arithmetic.EncLinkFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The loop controller changes only its coordinate scratch cell. -/
theorem encLinkControlState_ram (memory : Memory) :
    (encLinkControlState memory).1.ram =
      if memory.registers 2 = 254#256 then Function.update memory.ram 35 (memory.ram 36)
      else memory.ram := by
  unfold encLinkControlState
  split
  · rename_i zero
    rw [(encLinkReturn_state memory).2.1]
    simp [zero]
  · split
    · rename_i boundary
      rw [(encLinkSwitch_state (encLinkCompared memory)).1]
      simp [boundary, encLinkCompared]
    · rename_i other
      simp [other, encLinkCompared]

/-- The loop controller preserves every bit stack. -/
theorem encLinkControlState_bits (memory : Memory) :
    (encLinkControlState memory).1.bits = memory.bits := by
  unfold encLinkControlState
  split
  · exact (encLinkReturn_state memory).2.2
  · split
    · exact (encLinkSwitch_state (encLinkCompared memory)).2
    · rfl

/-- The output and control blocks preserve every bit stack. -/
theorem encLinkAfterQuery_bits (memory : Memory) :
    (encLinkAfterQuery memory).1.bits = memory.bits := by
  unfold encLinkAfterQuery
  split
  · rfl
  · exact (encLinkControlState_bits _).trans (encLinkFinish_bits memory)

/-- The accepted tail changes only one label and the loop scratch cells. -/
theorem encLinkAfterQuery_ram (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    let written := Function.update (Function.update (Function.update
      (Function.update memory.ram (memory.ram 33)
        ((memory.registers 8 ^^^ memory.ram 40) ^^^ memory.ram 41))
      33 (memory.ram 33 + 1)) 32 (memory.ram 32 + 1)) 38 (memory.ram 38 - 1)
    (encLinkAfterQuery memory).1.ram =
      if memory.ram 38 - 1 = 254#256 then Function.update written 35 (written 36)
      else written := by
  simp only [encLinkAfterQuery, if_neg accepted]
  rw [encLinkControlState_ram, encLinkFinish_counter memory countSafe,
    encLinkFinish_ram memory inputSafe countSafe]
  rfl

/-- The accepted tail retains every cell outside its writes. -/
theorem encLinkAfterQuery_frame (memory : Memory) (cell : Word)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (outputSeparate : cell ≠ memory.ram 33)
    (scratchSeparate : cell ≠ 32 ∧ cell ≠ 33 ∧ cell ≠ 35 ∧ cell ≠ 38) :
    (encLinkAfterQuery memory).1.ram cell = memory.ram cell := by
  by_cases rejected : memory.registers 7 = 0#256
  · simp [encLinkAfterQuery, rejected]
  · rw [encLinkAfterQuery_ram memory rejected inputSafe countSafe]
    split <;> simp only [Function.update_apply, outputSeparate, scratchSeparate.1,
      scratchSeparate.2.1, scratchSeparate.2.2.1, scratchSeparate.2.2.2, if_false]

/-- The accepted tail advances both label cursors and its remaining count. -/
theorem encLinkAfterQuery_cursors (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (encLinkAfterQuery memory).1.ram 32 = memory.ram 32 + 1 ∧
    (encLinkAfterQuery memory).1.ram 33 = memory.ram 33 + 1 ∧
    (encLinkAfterQuery memory).1.ram 38 = memory.ram 38 - 1 := by
  rw [encLinkAfterQuery_ram memory accepted inputSafe countSafe]
  split <;> simp

/-- The accepted tail stores the selected transformed label. -/
theorem encLinkAfterQuery_output (memory : Memory)
    (accepted : memory.registers 7 ≠ 0#256)
    (separate : memory.ram 33 ≠ 32 ∧ memory.ram 33 ≠ 33 ∧
      memory.ram 33 ≠ 35 ∧ memory.ram 33 ≠ 38) :
    (encLinkAfterQuery memory).1.ram (memory.ram 33) =
      (memory.registers 8 ^^^ memory.ram 40) ^^^ memory.ram 41 := by
  rw [encLinkAfterQuery_ram memory accepted separate.1 separate.2.2.2]
  split <;> simp only [Function.update_apply, separate.1, separate.2.1,
    separate.2.2.1, separate.2.2.2, if_false, if_true]

end Kriterion.ArgoMAC.ArithmeticSimulator
