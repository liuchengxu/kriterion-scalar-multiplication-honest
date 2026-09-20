import Construction.Simulator.FreshChoice
import Construction.Simulator.InstallFresh
import Construction.Simulator.SwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

def freshQueryChoiceLabels (pc : Fin 67) : Fin 115 := ⟨pc.val, by omega⟩
def freshQuerySwapLabels (pc : Fin 14) : Fin 115 := ⟨pc.val + 71, by omega⟩

/-- The fresh query samples an unused output position and installs both sparse transpositions.
Register eight returns the answer. Register seven returns the acceptance flag.
Registers zero through five return the updated permutation metadata. -/
def freshQuery (attempts : Nat) : Machine := ⟨114,
  Vector.ofFn (fun pc : Fin 115 =>
    if choosing : pc.val < 66 then
      relocate freshQueryChoiceLabels
        ((freshChoice attempts).code[pc.val]'(by change pc.val < 67; omega))
    else if scanning : 71 ≤ pc.val ∧ pc.val < 84 then
      relocate freshQuerySwapLabels (swapTable.code[pc.val - 71]'(by change pc.val - 71 < 14; omega))
    else if installing : 84 ≤ pc.val ∧ pc.val < 114 then
      (installFresh[pc.val - 84]'(by change pc.val - 84 < 30; omega)).emit ⟨pc.val + 1, by omega⟩
    else match pc.val with
      | 66 => .branch 7 114 67
      | 67 => .constant 6 0 68
      | 68 => .arithmetic .add 8 9 6 69
      | 69 => .arithmetic .add 9 3 6 70
      | 70 => .arithmetic .add 10 4 6 71
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
