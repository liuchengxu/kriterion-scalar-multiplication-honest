import Construction.Simulator.LinearProgram

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The retarget update changes only the first field word.
Register zero holds the requested result. Register one holds the old result.
Register ten points to the target table. -/
def retargetLow : List LinearInstruction :=
  [.load 2 10, .arithmetic .fieldSub 0 0 1, .arithmetic .fieldAdd 0 0 2, .store 10 0]

end Kriterion.ArgoMAC.ArithmeticSimulator
