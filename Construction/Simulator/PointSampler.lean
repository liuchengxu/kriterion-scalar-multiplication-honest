import Construction.Simulator.RuntimeSampler
import Construction.Simulator.ScalarMul

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The point sampler starts its bounded integer sampler after the range constant. -/
def pointSamplerRetryLabels (pc : Fin 32) : Fin 48 := ⟨pc.val + 1, by omega⟩

/-- The point sampler starts scalar multiplication after the generator constants. -/
def pointSamplerMulLabels (pc : Fin 11) : Fin 48 := ⟨pc.val + 37, by omega⟩

/-- The point sampler multiplies the standard generator by one bounded scalar draw.
The sampler uses scalar zero if its rejection limit expires. -/
def pointSampler (attempts : Nat) : Machine := ⟨47,
  Vector.ofFn (fun pc : Fin 48 =>
    if sampler : 0 < pc.val ∧ pc.val < 32 then
      relocate pointSamplerRetryLabels ((runtimeSampler attempts).code[pc.val - 1]'(by change pc.val - 1 < 32; omega))
    else if multiply : 37 ≤ pc.val ∧ pc.val < 47 then
      relocate pointSamplerMulLabels (scalarMul.code[pc.val - 37]'(by change pc.val - 37 < 11; omega))
    else match pc.val with
      | 0 => .constant 5 (BitVec.ofNat 256 BN254.scalarFieldModulus) 1
      | 32 => .branch 7 33 34
      | 33 => .constant 0 0 34
      | 34 => .constant 5 1 35
      | 35 => .constant 6 1 36
      | 36 => .constant 7 2 37
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
