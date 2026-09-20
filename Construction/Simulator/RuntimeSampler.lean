import Construction.Simulator.RuntimeTrial

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The retry program places the runtime trial after its entry instruction. -/
def runtimeRetryLabels (pc : Fin 27) : Fin 32 := ⟨pc.val + 1, by omega⟩

/-- The sampler reads its range from register five and stores its retry count in register four. -/
def runtimeSampler (attempts : Nat) : Machine := ⟨31,
  Vector.ofFn (fun pc : Fin 32 =>
    if inside : 0 < pc.val ∧ pc.val < 27 then
      relocate runtimeRetryLabels (runtimeTrial.code[pc.val - 1]'(by change pc.val - 1 < 27; omega))
    else match pc.val with
      | 0 => .constant 4 (BitVec.ofNat 256 attempts) 29
      | 27 => .branch 7 28 31
      | 28 => .arithmetic .sub 4 4 1 29
      | 29 => .branch 4 30 1
      | 30 => .constant 7 0 31
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
