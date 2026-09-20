import Construction.Simulator.HashLift
import Construction.Simulator.PadBlocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The input block adds the fixed gate tweak to the selected label. -/
def gateTweakProgram (tweak : Block) : List LinearInstruction :=
  [.constant 2 (tweak.setWidth 256), .arithmetic .xor 9 9 2]

/-- The hash range block computes all three selected permutation targets. -/
def gateHashRanges : List LinearInstruction :=
  [.arithmetic .xor 4 4 9, .arithmetic .xor 5 5 9, .arithmetic .xor 6 6 9, .constant 7 3]

/-- The pad range block computes both selected permutation targets. -/
def gatePadRanges : List LinearInstruction :=
  [.arithmetic .xor 4 4 9, .arithmetic .xor 5 5 9, .constant 7 2]

/-- The false branch returns three hash-slot targets. -/
def gateHashProgram (tweak : Block) : List LinearInstruction :=
  gateTweakProgram tweak ++ hashLiftProgram ++ gateHashRanges

/-- The true branch returns two pad-slot targets. -/
def gatePadProgram (tweak : Block) : List LinearInstruction :=
  gateTweakProgram tweak ++ padBlocksProgram ++ gatePadRanges

end Kriterion.ArgoMAC.ArithmeticSimulator
