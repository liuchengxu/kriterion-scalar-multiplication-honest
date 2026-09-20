import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The machine negates a canonical point in registers two through four.
Register zero becomes zero. -/
def pointNegation : Machine := ⟨3, #v[
  .constant 0 0 1,
  .branch 2 3 2,
  .arithmetic .fieldSub 4 0 4 3,
  .halt], by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
