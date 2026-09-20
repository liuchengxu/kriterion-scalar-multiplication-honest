import Construction.Simulator.IntegerTrial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The retry program places the trial after its entry instruction. -/
def retryLabels (pc : Fin 20) : Fin 25 := ⟨pc.val + 1, by omega⟩

/-- The sampler stores its remaining retries in register four.
The sampler returns its acceptance flag in register seven.
A zero flag marks an exhausted retry limit. -/
def boundedSampler (size attempts : Nat) : Machine := ⟨24,
  Vector.ofFn (fun pc : Fin 25 =>
    if inside : 0 < pc.val ∧ pc.val < 20 then
      relocate retryLabels ((boundedTrial size).code[pc.val - 1]'(by change pc.val - 1 < 20; omega))
    else match pc.val with
      | 0 => .constant 4 (BitVec.ofNat 256 attempts) 22
      | 20 => .branch 7 21 24
      | 21 => .arithmetic .sub 4 4 1 22
      | 22 => .branch 4 23 1
      | 23 => .constant 7 0 24
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
