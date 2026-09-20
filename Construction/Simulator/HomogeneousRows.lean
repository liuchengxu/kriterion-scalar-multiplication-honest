import Construction.Simulator.HomogeneousPoint
import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each row contains the fixed homogeneous conversion block. -/
def homogeneousRowLabels {count : Nat} (index : Fin (count + 1)) (pc : Fin 9) : Fin (25 * (count + 1) + 2) :=
  ⟨1 + 25 * index.val + 10 + pc.val, by have i := index.isLt; have p := pc.isLt; omega⟩

/-- The machine stores the first accumulator point and the free RAM points as homogeneous rows.
Register ten points to the free points. Register eleven points to the scales.
Register thirteen points to the destination. The first row uses registers two through four. -/
def homogeneousRows (count : Nat) (fits : 25 * (count + 1) + 1 < 2 ^ 256) : Machine :=
  ⟨25 * (count + 1) + 1, Vector.ofFn (fun pc : Fin (25 * (count + 1) + 2) =>
    if first : pc.val = 0 then .constant 12 1 ⟨8, by omega⟩
    else if inside : pc.val < 25 * (count + 1) + 1 then
      let index : Fin (count + 1) := ⟨(pc.val - 1) / 25, by omega⟩
      let slot := (pc.val - 1) % 25
      let labelAt (position : Nat) (bound : position < 25) : Fin (25 * (count + 1) + 2) :=
        ⟨1 + 25 * index.val + position, by have i := index.isLt; omega⟩
      if slot = 0 then .constant 8 (BitVec.ofNat 256 (3 * (index.val - 1))) (labelAt 1 (by decide))
      else if slot = 1 then .arithmetic .add 8 10 8 (labelAt 2 (by decide))
      else if slot = 2 then .load 2 8 (labelAt 3 (by decide))
      else if slot = 3 then .arithmetic .add 8 8 12 (labelAt 4 (by decide))
      else if slot = 4 then .load 3 8 (labelAt 5 (by decide))
      else if slot = 5 then .arithmetic .add 8 8 12 (labelAt 6 (by decide))
      else if slot = 6 then .load 4 8 (labelAt 7 (by decide))
      else if slot = 7 then .constant 8 (BitVec.ofNat 256 index.val) (labelAt 8 (by decide))
      else if slot = 8 then .arithmetic .add 8 11 8 (labelAt 9 (by decide))
      else if slot = 9 then .load 0 8 (labelAt 10 (by decide))
      else if conversion : slot < 18 then
        relocate (homogeneousRowLabels index) (homogeneousPoint.code[slot - 10]'(by change slot - 10 < 9; omega))
      else if slot = 18 then .constant 8 (BitVec.ofNat 256 (3 * index.val)) (labelAt 19 (by decide))
      else if slot = 19 then .arithmetic .add 8 13 8 (labelAt 20 (by decide))
      else if slot = 20 then .store 8 5 (labelAt 21 (by decide))
      else if slot = 21 then .arithmetic .add 8 8 12 (labelAt 22 (by decide))
      else if slot = 22 then .store 8 6 (labelAt 23 (by decide))
      else if slot = 23 then .arithmetic .add 8 8 12 (labelAt 24 (by decide))
      else .store 8 7 ⟨1 + 25 * (index.val + 1), by have i := index.isLt; omega⟩
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
