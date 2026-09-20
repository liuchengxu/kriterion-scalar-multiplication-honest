import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The save block uses scratch cells zero through six.
The block retains the six metadata registers and the inverse position. -/
def oracleSave : List LinearInstruction :=
  [.constant 15 0, .store 15 0, .constant 15 1, .store 15 1,
    .constant 15 2, .store 15 2, .constant 15 3, .store 15 3,
    .constant 15 4, .store 15 4, .constant 15 5, .store 15 5,
    .constant 15 6, .store 15 8]

/-- The restore block retains the sampled word in register nine.
The block restores metadata and the inverse position from scratch RAM.
Register seven retains the sampler's acceptance flag. -/
def oracleRestore : List LinearInstruction :=
  [.constant 15 0, .arithmetic .add 9 0 15,
    .constant 15 0, .load 0 15, .constant 15 1, .load 1 15,
    .constant 15 2, .load 2 15, .constant 15 3, .load 3 15,
    .constant 15 4, .load 4 15, .constant 15 5, .load 5 15,
    .constant 15 6, .load 8 15]

/-- The saved state changes only the scratch cells and the address register. -/
def oracleSaved (memory : Memory) : Memory :=
  { memory with
    registers := Function.update memory.registers 15 6
    ram := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update memory.ram 0 (memory.registers 0))
        1 (memory.registers 1)) 2 (memory.registers 2)) 3 (memory.registers 3))
        4 (memory.registers 4)) 5 (memory.registers 5)) 6 (memory.registers 8) }

/-- The restored state retains the sampled value and every RAM cell. -/
def oracleRestored (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update memory.registers 9 (memory.registers 0))
          0 (memory.ram 0)) 1 (memory.ram 1)) 2 (memory.ram 2)) 3 (memory.ram 3))
          4 (memory.ram 4)) 5 (memory.ram 5)) 8 (memory.ram 6)) 15 6 }

end Kriterion.ArgoMAC.ArithmeticSimulator
