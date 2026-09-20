import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The pad program combines a field target in register zero with its ciphertext in register eight.
The program returns its two 128-bit blocks in registers four and five. -/
def padBlocksProgram : List LinearInstruction :=
  [.arithmetic .xor 8 8 0, .constant 2 (BitVec.ofNat 256 (2 ^ 128 - 1)), .arithmetic .and 4 8 2,
    .constant 3 128, .arithmetic .shiftRight 5 8 3]

end Kriterion.ArgoMAC.ArithmeticSimulator
