import Construction.Simulator.PointHorner
import Construction.Simulator.PointNegation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The scalar block precedes the canonical point write. -/
def clampScalarLabels (pc : Fin 11) : Fin 27 := ⟨pc.val + 1, by omega⟩

/-- The negation block follows the canonical point write. -/
def clampNegationLabels (pc : Fin 4) : Fin 27 := ⟨13 + pc.val, by omega⟩

/-- The machine subtracts the radix multiple from the selected output.
Register eleven points to the five-word online input record.
Registers two through four receive the canonical correction point. -/
def clampPoint : Machine := ⟨26, Vector.ofFn (fun pc : Fin 27 =>
  if pc.val = 0 then .constant 0 (BitVec.ofNat 256 radix.val) 1
  else if scalar : pc.val < 11 then
    relocate clampScalarLabels (scalarMul.code[pc.val - 1]'(by change pc.val - 1 < 11; omega))
  else if pc.val = 11 then .constant 5 0 12
  else if pc.val = 12 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple 13
  else if negation : pc.val < 16 then
    relocate clampNegationLabels (pointNegation.code[pc.val - 13]'(by change pc.val - 13 < 4; omega))
  else if pc.val = 16 then .constant 8 2 17
  else if pc.val = 17 then .arithmetic .add 8 11 8 18
  else if pc.val = 18 then .load 5 8 19
  else if pc.val = 19 then .constant 1 1 20
  else if pc.val = 20 then .arithmetic .and 5 5 1 21
  else if pc.val = 21 then .arithmetic .add 8 8 1 22
  else if pc.val = 22 then .load 6 8 23
  else if pc.val = 23 then .arithmetic .add 8 8 1 24
  else if pc.val = 24 then .load 7 8 25
  else if pc.val = 25 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple 26
  else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
