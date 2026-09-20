import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The program reads the range bound from register five.
A zero bound denotes the full word range.
The program prepares registers zero through three for the sampling loop. -/
def rangeWidth : Machine := ⟨9, #v[
  .constant 0 0 1,
  .constant 1 1 2,
  .constant 2 0 3,
  .arithmetic .add 3 5 2 4,
  .branch 3 7 5,
  .arithmetic .add 2 2 1 6,
  .arithmetic .shiftRight 3 3 1 4,
  .branch 5 8 9,
  .constant 2 256 9,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
