import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The input block reads stack zero in little-endian order.
Register zero stores the value. Register seven records success. -/
def wordInput (width : Nat) : Machine := ⟨14, #v[
  .constant 0 0 1, .constant 1 1 2, .constant 2 (BitVec.ofNat 256 width) 3,
  .constant 4 1 4, .branch 2 11 5, .pop 0 13 6 7,
  .constant 3 0 8, .constant 3 1 8, .arithmetic .mul 3 3 1 9,
  .arithmetic .add 0 0 3 10, .arithmetic .add 1 1 1 12,
  .constant 7 1 14, .arithmetic .sub 2 2 4 4, .constant 7 0 14,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
