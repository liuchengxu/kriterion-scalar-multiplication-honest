import Construction.Simulator.LinearProgram
import Construction.Simulator.ReverseSwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The setup reads the input table address and count from registers one and two. -/
def inverseProbeSetup : List LinearInstruction :=
  [.constant 7 0, .constant 6 2, .arithmetic .mul 9 2 6,
    .arithmetic .add 9 1 9, .arithmetic .sub 9 9 6, .arithmetic .add 10 2 7]

/-- The probe computes an inverse position and checks the used prefix.
Register zero supplies the used count. Register eight supplies the query.
Register eight returns the position. Register seven returns the known-input flag. -/
def inverseProbe : Machine := ⟨21, #v[
  .constant 7 0 1,
  .constant 6 2 2,
  .arithmetic .mul 9 2 6 3,
  .arithmetic .add 9 1 9 4,
  .arithmetic .sub 9 9 6 5,
  .arithmetic .add 10 2 7 6,
  .constant 15 3 20,
  .branch 10 19 8,
  .load 11 9 9,
  .arithmetic .add 9 9 14 10,
  .load 12 9 11,
  .arithmetic .xor 13 8 11 12,
  .branch 13 15 13,
  .arithmetic .xor 13 8 12 14,
  .branch 13 16 17,
  .arithmetic .add 8 12 13 17,
  .arithmetic .add 8 11 13 17,
  .arithmetic .sub 9 9 15 18,
  .arithmetic .sub 10 10 14 7,
  .arithmetic .less 7 8 0 21,
  .constant 14 1 7,
  .halt], by decide⟩

def inverseProbeLabels (pc : Fin 15) : Fin 22 := ⟨pc.val + 6, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
