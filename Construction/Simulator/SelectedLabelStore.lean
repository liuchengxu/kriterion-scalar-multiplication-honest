import Construction.Simulator.SelectedLabels

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The store copies one selected label to the caller's label region. -/
def selectedLabelStore (index : Fin 508) : List LinearInstruction :=
  labelSelect index ++ [.constant 0 (BitVec.ofNat 256 index.val),
    .arithmetic .add 0 14 0, .store 0 8]

/-- The program stores the selected labels in x-then-y order. -/
def selectedLabelStores (indices : List (Fin 508)) : List LinearInstruction :=
  indices.flatMap selectedLabelStore

/-- The complete program stores all 508 labels. -/
def selectedLabelStoreProgram : List LinearInstruction :=
  selectedLabelStores (List.finRange 508)

end Kriterion.ArgoMAC.ArithmeticSimulator
