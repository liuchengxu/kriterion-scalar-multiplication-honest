import Construction.Simulator.PairStore

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The installation prepends the new input and output transpositions.
The block reads the inverse and chosen positions from scratch cells six and seven.
The block preserves the answer in register eight and increments the used count. -/
def installFresh : List LinearInstruction :=
  [.constant 6 0, .arithmetic .add 13 8 6,
    .constant 15 6, .load 11 15, .constant 15 7, .load 12 15,
    .constant 14 2, .arithmetic .sub 9 1 14, .arithmetic .add 8 0 6,
    .arithmetic .add 10 11 6] ++ pairStore ++
  [.arithmetic .add 1 9 6, .arithmetic .add 2 2 14, .constant 14 2,
    .arithmetic .sub 9 3 14, .arithmetic .add 8 0 6, .arithmetic .add 10 12 6] ++ pairStore ++
  [.arithmetic .add 3 9 6, .arithmetic .add 4 4 14,
    .arithmetic .add 0 0 14, .arithmetic .add 8 13 6]

/-- The source changes the four new table cells and returns updated metadata. -/
def installedFresh (memory : Memory) : Memory :=
  let inputAddress := memory.registers 1 - 2#256
  let outputAddress := memory.registers 3 - 2#256
  { memory with
    registers := Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
        memory.registers 0 (memory.registers 0 + 1#256)) 1 inputAddress)
        2 (memory.registers 2 + 1#256)) 3 outputAddress) 4 (memory.registers 4 + 1#256)) 6 0)
        9 outputAddress) 10 (memory.ram 7)) 11 (memory.ram 6)) 12 (memory.ram 7))
        13 (memory.registers 8)) 14 1) 15 7
    ram := Function.update (Function.update (Function.update (Function.update memory.ram
      inputAddress (memory.registers 0)) (inputAddress + 1#256) (memory.ram 6))
      outputAddress (memory.registers 0)) (outputAddress + 1#256) (memory.ram 7) }

end Kriterion.ArgoMAC.ArithmeticSimulator
