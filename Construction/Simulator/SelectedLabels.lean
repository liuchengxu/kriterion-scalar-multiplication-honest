import Construction.Simulator.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The first 254 label positions use x. The remaining positions use y. -/
def selectedCoordinate (index : Fin 508) : Nat := if index.val < 254 then 0 else 1

/-- Each selected label uses the corresponding little-endian coordinate bit. -/
def selectedBit (index : Fin 508) : Nat := if index.val < 254 then index.val else index.val - 254

/-- The offline source stores each true label before its false label. -/
def selectedFalseOffset (index : Fin 508) : Nat :=
  if index.val < 254 then 510 + 2 * index.val else 2 + 2 * (index.val - 254)

/-- The selector reads the input through register twelve and the offline key through register eleven. -/
def labelSelect (index : Fin 508) : List LinearInstruction :=
  [.constant 0 (BitVec.ofNat 256 (selectedCoordinate index)),
   .arithmetic .add 0 12 0, .load 1 0, .constant 2 (BitVec.ofNat 256 (selectedBit index)),
   .arithmetic .shiftRight 1 1 2, .constant 3 1, .arithmetic .and 1 1 3,
   .constant 0 (BitVec.ofNat 256 (selectedFalseOffset index)), .arithmetic .sub 0 0 1,
   .arithmetic .add 0 11 0, .load 8 0]

/-- Each label segment selects one 128-bit block and emits its canonical bits. -/
def selectedLabelSegment (index : Fin 508) : List LinearInstruction := labelSelect index ++ wordOutput 128

/-- Reverse emission leaves all 508 selected labels in their original wire order. -/
def selectedLabelsProgram : List LinearInstruction :=
  (List.finRange 508).reverse.flatMap selectedLabelSegment

end Kriterion.ArgoMAC.ArithmeticSimulator
