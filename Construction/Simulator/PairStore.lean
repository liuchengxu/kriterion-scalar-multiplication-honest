import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The block stores registers eight and ten in consecutive RAM cells.
Register nine supplies the address and retains it. Register fourteen holds the increment. -/
def pairStore : List LinearInstruction :=
  [.store 9 8, .constant 14 1, .arithmetic .add 9 9 14, .store 9 10,
    .arithmetic .sub 9 9 14]

/-- The source writes one key-value pair and sets the increment register. -/
def pairStored (memory : Memory) : Memory :=
  { memory with
    registers := Function.update memory.registers 14 1
    ram := Function.update (Function.update memory.ram (memory.registers 9) (memory.registers 8))
      (memory.registers 9 + 1#256) (memory.registers 10) }

end Kriterion.ArgoMAC.ArithmeticSimulator
