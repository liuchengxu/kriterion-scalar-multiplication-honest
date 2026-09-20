import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The sampler appends one fair bit to register zero on each loop.
Registers one, two, and three store one, the remaining count, and the current bit.
The sampler preserves RAM and every stack. -/
def wordSampler (width : Nat) : Machine := ⟨12, #v[
  .constant 0 0 1,
  .constant 1 1 2,
  .constant 2 (BitVec.ofNat 256 width) 3,
  .branch 2 11 4,
  .coin 1 5,
  .pop 1 12 6 7,
  .constant 3 0 8,
  .constant 3 1 8,
  .arithmetic .add 0 0 0 9,
  .arithmetic .add 0 0 3 10,
  .arithmetic .sub 2 2 1 3,
  .constant 3 0 12,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
