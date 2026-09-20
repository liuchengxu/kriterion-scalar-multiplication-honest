import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each fold step reads one field word and updates the binary field accumulator. -/
def fieldFoldStep (index : Nat) : List LinearInstruction :=
  [.constant 2 (BitVec.ofNat 256 index), .arithmetic .add 2 10 2, .load 1 2,
    .arithmetic .fieldMul 0 3 0, .arithmetic .fieldAdd 0 0 1]

/-- The fold visits the field words in reverse order. -/
def fieldFoldBody : Nat → Nat → List LinearInstruction
  | 0, _ => []
  | count + 1, start => fieldFoldBody count (start + 1) ++ fieldFoldStep start

/-- The field fold initializes the accumulator and its fixed multiplier. -/
def fieldFold (count start : Nat) : List LinearInstruction :=
  [.constant 0 0, .constant 3 2] ++ fieldFoldBody count start

end Kriterion.ArgoMAC.ArithmeticSimulator
