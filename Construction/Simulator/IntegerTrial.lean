import Construction.Simulator.Assembly
import Construction.Simulator.WordSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The assembler retains the sampler labels in the trial program. -/
def trialLabels (pc : Fin 13) : Fin 20 := ⟨pc.val, by omega⟩

/-- The trial stores its acceptance flag in register seven.
The full-range path samples one extra bit.
The narrow path compares the sampled word with the bound. -/
def integerTrial (width : Nat) (bound : Word) (full : Bool) : Machine := ⟨19,
  Vector.ofFn (fun pc : Fin 20 =>
    if inside : pc.val < 12 then
      relocate trialLabels ((wordSampler width).code[pc.val]'(by change pc.val < 13; omega))
    else match pc.val with
      | 12 => if full then .coin 1 13 else .constant 6 0 17
      | 13 => .pop 1 19 14 15
      | 14 => .constant 6 0 16
      | 15 => .constant 6 1 16
      | 16 => .arithmetic .less 7 6 1 19
      | 17 => .constant 5 bound 18
      | 18 => .arithmetic .less 7 0 5 19
      | _ => .halt), by decide⟩

/-- This program selects the narrow or full-word trial from the requested range. -/
def boundedTrial (size : Nat) : Machine :=
  integerTrial (min (size.log2 + 1) 256) (BitVec.ofNat 256 size) (size == 2 ^ 256)

end Kriterion.ArgoMAC.ArithmeticSimulator
