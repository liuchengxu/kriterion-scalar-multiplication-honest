import Construction.Simulator.ScalarMul

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The machine scales the canonical point in registers two through four.
Register zero contains the nonzero scale.
Registers five through seven receive homogeneous coordinates. -/
def homogeneousPoint : Machine := ⟨8, #v[
  .constant 8 0 1,
  .branch 2 2 5,
  .constant 5 0 3,
  .constant 7 0 4,
  .arithmetic .add 6 0 8 8,
  .arithmetic .fieldMul 5 3 0 6,
  .arithmetic .fieldMul 6 4 0 7,
  .arithmetic .add 7 0 8 8,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
