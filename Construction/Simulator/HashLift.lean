import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The first block splits both inputs into 128-bit limbs. -/
def hashLiftSplit : List LinearInstruction :=
  [.constant 2 (BitVec.ofNat 256 (2 ^ 128 - 1)), .constant 3 128,
    .arithmetic .and 4 0 2, .arithmetic .shiftRight 0 0 3,
    .arithmetic .and 5 1 2, .arithmetic .shiftRight 1 1 3,
    .constant 6 (BitVec.ofNat 256 (BN254.baseFieldModulus % 2 ^ 128)),
    .constant 7 (BitVec.ofNat 256 (BN254.baseFieldModulus / 2 ^ 128))]

/-- The low block computes the low limb and its carry. -/
def hashLiftLow : List LinearInstruction :=
  [.arithmetic .mul 8 6 5, .arithmetic .add 8 8 4,
    .arithmetic .and 4 8 2, .arithmetic .shiftRight 8 8 3]

/-- The middle block adds both cross products and both input carries. -/
def hashLiftMiddle : List LinearInstruction :=
  [.arithmetic .mul 6 6 1, .arithmetic .mul 5 7 5,
    .arithmetic .add 5 5 6, .arithmetic .add 5 5 0, .arithmetic .add 5 5 8]

/-- The high block computes the middle and high output limbs. -/
def hashLiftUpper : List LinearInstruction :=
  [.arithmetic .shiftRight 6 5 3, .arithmetic .and 5 5 2,
    .arithmetic .mul 7 7 1, .arithmetic .add 6 6 7]

/-- The lift program returns three 128-bit limbs in low-to-high order.
Register zero holds the field target. Register one holds the quotient. -/
def hashLiftProgram : List LinearInstruction := hashLiftSplit ++ hashLiftLow ++ hashLiftMiddle ++ hashLiftUpper

end Kriterion.ArgoMAC.ArithmeticSimulator
