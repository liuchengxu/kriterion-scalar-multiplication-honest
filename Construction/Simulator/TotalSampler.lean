import Construction.Simulator.RuntimeSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The total sampler retains the runtime sampler's instruction positions. -/
def totalSamplerRetryLabels (pc : Fin 32) : Fin 36 := ⟨pc.val, by omega⟩

/-- The total sampler adds a fixed offset after its explicit zero fallback.
The range stays in register five.
The result stays in register zero. -/
def totalSampler (attempts : Nat) (offset : Word) : Machine := ⟨35,
  Vector.ofFn (fun pc : Fin 36 =>
    if sampler : pc.val < 31 then
      relocate totalSamplerRetryLabels ((runtimeSampler attempts).code[pc.val]'(by change pc.val < 32; omega))
    else match pc.val with
      | 31 => .branch 7 32 33
      | 32 => .constant 0 0 33
      | 33 => .constant 6 offset 34
      | 34 => .arithmetic .add 0 0 6 35
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
