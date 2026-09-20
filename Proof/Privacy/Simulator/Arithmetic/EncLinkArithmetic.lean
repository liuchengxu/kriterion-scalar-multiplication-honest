import Construction.Simulator.EncLinkArithmetic
import Proof.Privacy.Simulator.Arithmetic.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block retains the bridge key and stores the complete caller state. -/
theorem encLinkSave_state (memory : Memory) :
    let final := executeLinear encLinkSave memory
    final.registers 8 = memory.registers 8 ∧ final.registers 9 = 15748 ∧ final.registers 10 = 4 ∧
    final.ram 32 = memory.registers 11 ∧ final.ram 33 = memory.registers 14 ∧
    final.ram 34 = memory.registers 14 ∧ final.ram 35 = memory.registers 12 ∧
    final.ram 36 = memory.registers 13 ∧ final.ram 38 = 508 ∧ final.bits = memory.bits := by
  simp [encLinkSave, executeLinear, LinearInstruction.execute]

/-- The hash-key split writes exactly the two packed blocks and preserves all stacks. -/
theorem encLinkWhitening_state (memory : Memory) :
    let final := executeLinear encLinkWhitening memory
    final.ram = Function.update (Function.update memory.ram 39 (memory.registers 8 >>> 128))
      40 (memory.registers 8 &&& BitVec.ofNat 256 (2 ^ 128 - 1)) ∧ final.bits = memory.bits := by
  simp [encLinkWhitening, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The call preparation uses the low coordinate bit and the first whitening key. -/
theorem encLinkPrepare_state (memory : Memory) :
    let final := executeLinear encLinkPrepare memory
    final.registers 8 = (memory.ram 35 &&& 1#256) ^^^ memory.ram 39 ∧
    final.registers 9 = memory.registers 0 ∧ final.registers 10 = 2 ∧
    final.ram = Function.update (Function.update memory.ram 41 (memory.ram (memory.ram 32)))
      35 (memory.ram 35 >>> 1) ∧ final.bits = memory.bits := by
  simp [encLinkPrepare, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The finish block applies the second key and selected label to the accepted oracle reply. -/
theorem encLinkFinish_value (memory : Memory) :
    (executeLinear encLinkFinish memory).registers 8 =
      (memory.registers 8 ^^^ memory.ram 40) ^^^ memory.ram 41 := by
  simp [encLinkFinish, executeLinear, LinearInstruction.execute, Arithmetic.eval]

/-- The finish block writes one label and updates the two cursors and counter. -/
theorem encLinkFinish_ram (memory : Memory)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (executeLinear encLinkFinish memory).ram =
      Function.update (Function.update (Function.update
        (Function.update memory.ram (memory.ram 33)
          ((memory.registers 8 ^^^ memory.ram 40) ^^^ memory.ram 41))
        33 (memory.ram 33 + 1)) 32 (memory.ram 32 + 1)) 38 (memory.ram 38 - 1) := by
  simp [encLinkFinish, executeLinear, LinearInstruction.execute, Arithmetic.eval,
    Function.update_of_ne inputSafe.symm, Function.update_of_ne countSafe.symm]

/-- The finish block returns the decreased loop count in register two. -/
theorem encLinkFinish_counter (memory : Memory)
    (countSafe : memory.ram 33#256 ≠ 38#256) :
    (executeLinear encLinkFinish memory).registers 2 = memory.ram 38#256 - 1#256 := by
  simp [encLinkFinish, executeLinear, LinearInstruction.execute, Arithmetic.eval,
    Function.update_of_ne countSafe.symm]

/-- Every linear link block preserves all bit stacks. -/
theorem encLinkFinish_bits (memory : Memory) :
    (executeLinear encLinkFinish memory).bits = memory.bits := by
  simp [encLinkFinish, executeLinear, LinearInstruction.execute]

/-- The coordinate switch replaces only the current coordinate bits in RAM. -/
theorem encLinkSwitch_state (memory : Memory) :
    (executeLinear encLinkSwitch memory).ram = Function.update memory.ram 35 (memory.ram 36) ∧
    (executeLinear encLinkSwitch memory).bits = memory.bits := by
  simp [encLinkSwitch, executeLinear, LinearInstruction.execute]

/-- The return block restores the requested output base and preserves all data. -/
theorem encLinkReturn_state (memory : Memory) :
    let final := executeLinear encLinkReturn memory
    final.registers 14 = memory.ram 34 ∧ final.ram = memory.ram ∧ final.bits = memory.bits := by
  simp [encLinkReturn, executeLinear, LinearInstruction.execute]

/-- The fixed linear blocks have exact instruction counts. -/
theorem encLinkArithmetic_lengths :
    encLinkSave.length = 15 ∧ encLinkWhitening.length = 8 ∧ encLinkPrepare.length = 17 ∧
    encLinkFinish.length = 20 ∧ encLinkSwitch.length = 4 ∧ encLinkReturn.length = 2 := by decide

end Kriterion.ArgoMAC.ArithmeticSimulator
