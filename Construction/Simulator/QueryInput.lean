import Construction.Simulator.Assembly
import Construction.Simulator.WordInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each input block has fourteen instructions and one caller return label. -/
def queryInputLabels (offset : Fin 83) (returnLabel : Fin 97) (pc : Fin 15) : Fin 97 :=
  if inside : pc.val < 14 then ⟨offset.val + pc.val, by have := offset.isLt; omega⟩
  else returnLabel

/-- The reader returns the query tag in register ten and the oracle index in register nine.
The reader returns the operand in register eight and retains the unread input suffix. -/
def queryInput : Machine := ⟨96, Vector.ofFn (fun pc : Fin 97 =>
  if tag : pc.val < 14 then
    relocate (queryInputLabels 0 14) ((wordInput 3).code[pc.val]'(by change pc.val < 15; omega))
  else if fixed : 19 ≤ pc.val ∧ pc.val < 33 then
    relocate (queryInputLabels 19 33) ((wordInput 14).code[pc.val - 19]'(by change pc.val - 19 < 15; omega))
  else if enc : 38 ≤ pc.val ∧ pc.val < 52 then
    relocate (queryInputLabels 38 52) ((wordInput 9).code[pc.val - 38]'(by change pc.val - 38 < 15; omega))
  else if hash : 57 ≤ pc.val ∧ pc.val < 71 then
    relocate (queryInputLabels 57 71) ((wordInput 254).code[pc.val - 57]'(by change pc.val - 57 < 15; omega))
  else if block : 80 ≤ pc.val ∧ pc.val < 94 then
    relocate (queryInputLabels 80 94) ((wordInput 128).code[pc.val - 80]'(by change pc.val - 80 < 15; omega))
  else match pc.val with
    | 14 => .constant 15 0 15
    | 15 => .arithmetic .add 10 0 15 16
    | 16 => .constant 14 2 17
    | 17 => .arithmetic .less 6 10 14 18
    | 18 => .branch 6 35 19
    | 33 => .arithmetic .add 9 0 15 34
    | 34 => .constant 15 0 80
    | 35 => .constant 14 4 36
    | 36 => .arithmetic .less 6 10 14 37
    | 37 => .branch 6 56 38
    | 52 => .constant 14 15240 53
    | 53 => .arithmetic .add 9 0 14 54
    | 54 => .constant 15 0 80
    | 56 => .constant 9 15748 57
    | 71 => .arithmetic .add 8 0 15 96
    | 94 => .arithmetic .add 8 0 15 96
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
