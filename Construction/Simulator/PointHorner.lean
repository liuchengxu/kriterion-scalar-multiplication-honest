import Construction.Simulator.ScalarMul
import Construction.Simulator.Assembly
import Construction.ArgoMAC.Base7

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each Horner entry contains one scalar-multiplication block. -/
def hornerScalarLabels {count : Nat} (index : Fin count) (pc : Fin 11) : Fin (22 * count + 6) :=
  ⟨5 + 22 * index.val + 1 + pc.val, by have i := index.isLt; have p := pc.isLt; omega⟩

/-- The machine reads canonical point triples through register ten in reverse order.
Registers five through seven receive the Horner result.
The machine preserves RAM and registers ten, eleven, and thirteen through fifteen. -/
def pointHornerMachine (count : Nat) (fits : 22 * count + 5 < 2 ^ 256) : Machine := ⟨22 * count + 5,
  Vector.ofFn (fun pc : Fin (22 * count + 6) =>
    if first : pc.val = 0 then .constant 9 0 ⟨1, by omega⟩
    else if second : pc.val = 1 then .constant 12 1 ⟨2, by omega⟩
    else if third : pc.val = 2 then .constant 5 0 ⟨3, by omega⟩
    else if fourth : pc.val = 3 then .constant 6 0 ⟨4, by omega⟩
    else if fifth : pc.val = 4 then .constant 7 0 ⟨5, by omega⟩
    else if inside : pc.val < 22 * count + 5 then
      let index : Fin count := ⟨(pc.val - 5) / 22, by omega⟩
      let slot := (pc.val - 5) % 22
      let labelAt (position : Nat) (bound : position < 22) : Fin (22 * count + 6) :=
        ⟨5 + 22 * index.val + position, by have i := index.isLt; omega⟩
      if slot = 0 then .constant 0 (BitVec.ofNat 256 radix.val) (labelAt 1 (by decide))
      else if scalar : slot < 11 then
        relocate (hornerScalarLabels index) (scalarMul.code[slot - 1]'(by change slot - 1 < 11; omega))
      else if slot = 11 then .constant 8 (BitVec.ofNat 256 (3 * (count - 1 - index.val))) (labelAt 12 (by decide))
      else if slot = 12 then .arithmetic .add 8 10 8 (labelAt 13 (by decide))
      else if slot = 13 then .load 5 8 (labelAt 14 (by decide))
      else if slot = 14 then .arithmetic .add 8 8 12 (labelAt 15 (by decide))
      else if slot = 15 then .load 6 8 (labelAt 16 (by decide))
      else if slot = 16 then .arithmetic .add 8 8 12 (labelAt 17 (by decide))
      else if slot = 17 then .load 7 8 (labelAt 18 (by decide))
      else if slot = 18 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple (labelAt 19 (by decide))
      else if slot = 19 then .arithmetic .add 5 2 9 (labelAt 20 (by decide))
      else if slot = 20 then .arithmetic .add 6 3 9 (labelAt 21 (by decide))
      else .arithmetic .add 7 4 9 ⟨5 + 22 * (index.val + 1), by have i := index.isLt; omega⟩
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
