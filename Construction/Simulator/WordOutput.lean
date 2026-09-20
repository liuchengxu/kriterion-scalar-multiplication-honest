import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The output block copies register eight to stack three in little-endian order.
Registers nine and ten hold temporary values. Each output bit costs three instructions. -/
def wordOutput : Nat → List LinearInstruction
  | 0 => []
  | width + 1 =>
      [.constant 9 (BitVec.ofNat 256 width), .arithmetic .shiftRight 10 8 9,
        .pushBit 3 10] ++ wordOutput width

end Kriterion.ArgoMAC.ArithmeticSimulator
