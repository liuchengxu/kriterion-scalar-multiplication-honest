import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Registers two through four hold the accumulated point. -/
def scalarAccumulator : PointRegisters := ⟨2, 3, 4⟩

/-- Registers five through seven hold the current point multiple. -/
def scalarMultiple : PointRegisters := ⟨5, 6, 7⟩

/-- The machine multiplies the input point by the scalar in register zero.
The machine uses register one for its constant and register eight for its bit.
The machine returns the point in registers two through four. -/
def scalarMul : Machine := ⟨10, #v[
  .constant 1 1 1,
  .constant 2 0 2,
  .constant 3 0 3,
  .constant 4 0 4,
  .branch 0 10 5,
  .arithmetic .and 8 0 1 6,
  .branch 8 8 7,
  .pointAdd scalarAccumulator scalarAccumulator scalarMultiple 8,
  .pointAdd scalarMultiple scalarMultiple scalarMultiple 9,
  .arithmetic .shiftRight 0 0 1 4,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
