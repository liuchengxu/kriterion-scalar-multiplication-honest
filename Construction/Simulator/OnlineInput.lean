import Construction.Simulator.Assembly
import Construction.Simulator.WordInput
import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The online input block returns to its caller after fourteen instructions. -/
def onlineInputLabels (offset : Fin 84) (returnLabel : Fin 98) (pc : Fin 15) : Fin 98 :=
  if inside : pc.val < 14 then ⟨offset.val + pc.val, by have := offset.isLt; omega⟩
  else returnLabel

/-- The store writes the parsed word at a fixed offset from register ten. -/
def onlineInputStore (offset : Word) : List LinearInstruction :=
  [.constant 15 offset, .arithmetic .add 8 10 15, .store 8 0]

/-- The absent-point path writes both unused coordinates as zero. -/
def onlineInputZero : List LinearInstruction :=
  [.constant 0 0, .constant 15 3, .arithmetic .add 8 10 15, .store 8 0,
    .constant 15 4, .arithmetic .add 8 10 15, .store 8 0]

/-- The reader stores input x, input y, output tag, output x, and output y.
Register ten supplies the first RAM address.
Tags zero, two, and one denote no output, the identity, and an affine point. -/
def onlineInput : Machine := ⟨97, Vector.ofFn (fun pc : Fin 98 =>
  if first : pc.val < 14 then
    relocate (onlineInputLabels 0 14) ((wordInput 254).code[pc.val]'(by change pc.val < 15; omega))
  else if second : 17 ≤ pc.val ∧ pc.val < 31 then
    relocate (onlineInputLabels 17 31) ((wordInput 254).code[pc.val - 17]'(by change pc.val - 17 < 15; omega))
  else if tag : 34 ≤ pc.val ∧ pc.val < 48 then
    relocate (onlineInputLabels 34 48) ((wordInput 2).code[pc.val - 34]'(by change pc.val - 34 < 15; omega))
  else if pointX : 54 ≤ pc.val ∧ pc.val < 68 then
    relocate (onlineInputLabels 54 68) ((wordInput 254).code[pc.val - 54]'(by change pc.val - 54 < 15; omega))
  else if pointY : 71 ≤ pc.val ∧ pc.val < 85 then
    relocate (onlineInputLabels 71 85) ((wordInput 254).code[pc.val - 71]'(by change pc.val - 71 < 15; omega))
  else match pc.val with
    | 14 => .constant 15 0 15
    | 15 => .arithmetic .add 8 10 15 16
    | 16 => .store 8 0 17
    | 31 => .constant 15 1 32
    | 32 => .arithmetic .add 8 10 15 33
    | 33 => .store 8 0 34
    | 48 => .constant 15 2 49
    | 49 => .arithmetic .add 8 10 15 50
    | 50 => .store 8 0 51
    | 51 => .constant 15 1 52
    | 52 => .arithmetic .sub 6 0 15 53
    | 53 => .branch 6 54 90
    | 68 => .constant 15 3 69
    | 69 => .arithmetic .add 8 10 15 70
    | 70 => .store 8 0 71
    | 85 => .constant 15 4 86
    | 86 => .arithmetic .add 8 10 15 87
    | 87 => .store 8 0 97
    | 90 => .constant 0 0 91
    | 91 => .constant 15 3 92
    | 92 => .arithmetic .add 8 10 15 93
    | 93 => .store 8 0 94
    | 94 => .constant 15 4 95
    | 95 => .arithmetic .add 8 10 15 96
    | 96 => .store 8 0 97
    | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
