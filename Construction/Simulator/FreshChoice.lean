import Construction.Simulator.OracleScratch
import Construction.Simulator.RuntimeSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sampler occupies the middle of the fresh-query block. -/
def freshSamplerLabels (pc : Fin 32) : Fin 67 := ⟨pc.val + 15, by omega⟩

/-- The fresh-query block saves metadata, samples an unused rank, and restores metadata.
Register zero supplies the used count. Register five supplies the domain size.
Register nine returns the chosen position. Scratch cell seven also stores that position.
Register seven retains the sampler's acceptance flag. -/
def freshChoice (attempts : Nat) : Machine := ⟨66,
  Vector.ofFn (fun pc : Fin 67 =>
    if sampling : 15 ≤ pc.val ∧ pc.val < 46 then
      relocate freshSamplerLabels
        ((runtimeSampler attempts).code[pc.val - 15]'(by change pc.val - 15 < 32; omega))
    else match pc.val with
      | 0 => .constant 15 0 1
      | 1 => .store 15 0 2
      | 2 => .constant 15 1 3
      | 3 => .store 15 1 4
      | 4 => .constant 15 2 5
      | 5 => .store 15 2 6
      | 6 => .constant 15 3 7
      | 7 => .store 15 3 8
      | 8 => .constant 15 4 9
      | 9 => .store 15 4 10
      | 10 => .constant 15 5 11
      | 11 => .store 15 5 12
      | 12 => .constant 15 6 13
      | 13 => .store 15 8 14
      | 14 => .arithmetic .sub 5 5 0 15
      | 46 => .constant 15 0 47
      | 47 => .arithmetic .add 9 0 15 48
      | 48 => .constant 15 0 49
      | 49 => .load 0 15 50
      | 50 => .constant 15 1 51
      | 51 => .load 1 15 52
      | 52 => .constant 15 2 53
      | 53 => .load 2 15 54
      | 54 => .constant 15 3 55
      | 55 => .load 3 15 56
      | 56 => .constant 15 4 57
      | 57 => .load 4 15 58
      | 58 => .constant 15 5 59
      | 59 => .load 5 15 60
      | 60 => .constant 15 6 61
      | 61 => .load 8 15 62
      | 62 => .branch 7 66 63
      | 63 => .arithmetic .add 9 9 0 64
      | 64 => .constant 15 7 65
      | 65 => .store 15 9 66
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
