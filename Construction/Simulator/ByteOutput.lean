import Construction.Simulator.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The byte block returns to the RAM loop after its last bit. -/
def byteOutputLabels (index : Nat) : Fin 30 :=
  if inside : index < 24 then ⟨index + 5, by omega⟩ else 1

/-- The output loop reads consecutive RAM bytes in reverse order.
Register eleven supplies the first address. Register twelve supplies the byte count. -/
def byteOutput : Machine := ⟨29, Vector.ofFn (fun pc : Fin 30 =>
  if head : pc.val < 5 then
    (#v[Instruction.constant 13 1 1, .branch 12 29 2,
      .arithmetic .sub 12 12 13 3, .arithmetic .add 14 11 12 4,
      .load 8 14 5])[pc.val]'head
  else if body : pc.val < 29 then
    ((wordOutput 8)[pc.val - 5]'(by change pc.val - 5 < 24; omega)).emit
      (byteOutputLabels (pc.val - 5 + 1))
  else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
