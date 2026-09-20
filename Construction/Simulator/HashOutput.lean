import Construction.Simulator.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The shift selects the first block from the high half of the packed hash value. -/
def hashOutputShift : List LinearInstruction :=
  [.constant 9 128, .arithmetic .shiftRight 8 8 9]

/-- The output stack places the first block before the second block. -/
def hashOutput : List LinearInstruction :=
  wordOutput 128 ++ hashOutputShift ++ wordOutput 128

end Kriterion.ArgoMAC.ArithmeticSimulator
