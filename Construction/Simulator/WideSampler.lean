import Construction.Simulator.Assembly
import Construction.Simulator.WordSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The assembler retains the sampler labels in the larger program. -/
def wideLabels (pc : Fin 13) : Fin 17 := ⟨pc.val, by omega⟩

/-- The sampler stores the extra bit in register six.
The sampler preserves RAM, every stack, and the other caller registers. -/
def wideSampler (width : Nat) (extra : Bool) : Machine := ⟨16,
  Vector.ofFn (fun pc : Fin 17 =>
    if inside : pc.val < 12 then
      relocate wideLabels ((wordSampler width).code[pc.val]'(by change pc.val < 13; omega))
    else match pc.val with
      | 12 => if extra then .coin 1 13 else .constant 6 0 16
      | 13 => .pop 1 16 14 15
      | 14 => .constant 6 0 16
      | 15 => .constant 6 1 16
      | _ => .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
