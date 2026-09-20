import Construction.Simulator.SelectedLabels

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The selector reads the coordinate bit through the input record pointer. -/
def gateBitSelect (index : Fin 508) : List LinearInstruction :=
  [.constant 0 (BitVec.ofNat 256 (selectedCoordinate index)),
   .arithmetic .add 0 12 0, .load 1 0, .constant 2 (BitVec.ofNat 256 (selectedBit index)),
   .arithmetic .shiftRight 1 1 2, .constant 3 1, .arithmetic .and 1 1 3]

/-- The label reader uses the stored label region and saves the selected bit. -/
def gateLabelRead (index : Fin 508) : List LinearInstruction :=
  [.constant 0 (BitVec.ofNat 256 index.val), .arithmetic .add 0 14 0, .load 9 0,
   .constant 3 0, .arithmetic .add 10 1 3]

/-- The data reader loads one target, quotient, and table value. -/
def gateDataRead (target quotient table : Nat) : List LinearInstruction :=
  [.constant 2 (BitVec.ofNat 256 target), .arithmetic .add 2 11 2, .load 0 2,
   .constant 2 (BitVec.ofNat 256 quotient), .arithmetic .add 2 11 2, .load 1 2,
   .constant 2 (BitVec.ofNat 256 table), .arithmetic .add 2 11 2, .load 8 2]

/-- The loader prepares one gate directive from private RAM. -/
def gateDirectiveLoad (index : Fin 508) (target quotient table : Nat) : List LinearInstruction :=
  gateBitSelect index ++ gateLabelRead index ++ gateDataRead target quotient table

end Kriterion.ArgoMAC.ArithmeticSimulator
