import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The block exchanges input and output metadata for an inverse query.
The block preserves the used count, domain size, answer, and acceptance flag. -/
def swapMetadata : List LinearInstruction :=
  [.constant 6 0, .arithmetic .add 11 1 6, .arithmetic .add 1 3 6,
    .arithmetic .add 3 11 6, .arithmetic .add 11 2 6,
    .arithmetic .add 2 4 6, .arithmetic .add 4 11 6]

/-- The source exchanges both table addresses and both table counts. -/
def metadataSwapped (memory : Memory) : Memory :=
  { memory with registers := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update memory.registers 6 0)
        11 (memory.registers 2)) 1 (memory.registers 3)) 3 (memory.registers 1))
        2 (memory.registers 4)) 4 (memory.registers 2) }

end Kriterion.ArgoMAC.ArithmeticSimulator
