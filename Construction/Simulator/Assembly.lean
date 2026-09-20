import Cryptography.BoundedMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Assembly changes jump labels and retains every instruction operand. -/
def relocate {source target : Nat} (labels : Fin source → Fin target) :
    Instruction source → Instruction target
  | .halt => .halt
  | .push stack bit next => .push stack bit (labels next)
  | .pop stack empty zero one => .pop stack (labels empty) (labels zero) (labels one)
  | .coin stack next => .coin stack (labels next)
  | .constant register value next => .constant register value (labels next)
  | .arithmetic operation target left right next =>
      .arithmetic operation target left right (labels next)
  | .load target address next => .load target address (labels next)
  | .store address source next => .store address source (labels next)
  | .branch source zero nonzero => .branch source (labels zero) (labels nonzero)
  | .pushBit stack source next => .pushBit stack source (labels next)
  | .pointAdd target left right next => .pointAdd target left right (labels next)

end Kriterion.ArgoMAC.ArithmeticSimulator
