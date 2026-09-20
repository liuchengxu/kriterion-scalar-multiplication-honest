import Construction.Simulator.InverseProbe
import Construction.Simulator.SwapTable

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The known-query path composes the input inverse and output permutation.
Registers three and four supply the output table address and count.
Register seven returns zero for a fresh query and one for a known query. -/
def knownQuery : Machine := ⟨38, #v[
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
  .branch 7 38 22,
  .constant 6 0 23,
  .arithmetic .add 9 3 6 24,
  .arithmetic .add 10 4 6 25,
  .constant 14 1 26,
  .branch 10 38 27,
  .load 11 9 28,
  .arithmetic .add 9 9 14 29,
  .load 12 9 30,
  .arithmetic .xor 13 8 11 31,
  .branch 13 34 32,
  .arithmetic .xor 13 8 12 33,
  .branch 13 35 36,
  .arithmetic .add 8 12 13 36,
  .arithmetic .add 8 11 13 36,
  .arithmetic .add 9 9 14 37,
  .arithmetic .sub 10 10 14 26,
  .halt], by decide⟩

def knownProbeLabels (pc : Fin 22) : Fin 39 := ⟨pc.val, by omega⟩
def knownSwapLabels (pc : Fin 14) : Fin 39 := ⟨pc.val + 25, by omega⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
