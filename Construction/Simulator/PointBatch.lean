import Construction.Simulator.PointSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each point draw reserves its sampler, canonical write, and three RAM stores. -/
def pointBatchLabels {count : Nat} (index : Fin count) (pc : Fin 48) : Fin (58 * count + 1) :=
  ⟨58 * index.val + pc.val, by have i := index.isLt; have p := pc.isLt; omega⟩

/-- The point batch stores three canonical words per point through register ten.
Each point uses 58 charged instruction-table entries. -/
def pointBatch (count attempts : Nat) (fits : 58 * count < 2 ^ 256) : Machine := ⟨58 * count,
  Vector.ofFn (fun pc : Fin (58 * count + 1) =>
    if inside : pc.val < 58 * count then
      let index : Fin count := ⟨pc.val / 58, by omega⟩
      let slot := pc.val % 58
      let labelAt (position : Nat) (bound : position < 58) : Fin (58 * count + 1) :=
        ⟨58 * index.val + position, by have i := index.isLt; omega⟩
      if sampler : slot < 47 then
        relocate (pointBatchLabels index) ((pointSampler attempts).code[slot]'(by change slot < 48; omega))
      else if slot = 47 then .constant 5 0 (labelAt 48 (by decide))
      else if slot = 48 then .pointAdd scalarAccumulator scalarAccumulator scalarMultiple (labelAt 49 (by decide))
      else if slot = 49 then .constant 8 (BitVec.ofNat 256 (3 * index.val)) (labelAt 50 (by decide))
      else if slot = 50 then .arithmetic .add 8 10 8 (labelAt 51 (by decide))
      else if slot = 51 then .store 8 2 (labelAt 52 (by decide))
      else if slot = 52 then .constant 8 (BitVec.ofNat 256 (3 * index.val + 1)) (labelAt 53 (by decide))
      else if slot = 53 then .arithmetic .add 8 10 8 (labelAt 54 (by decide))
      else if slot = 54 then .store 8 3 (labelAt 55 (by decide))
      else if slot = 55 then .constant 8 (BitVec.ofNat 256 (3 * index.val + 2)) (labelAt 56 (by decide))
      else if slot = 56 then .arithmetic .add 8 10 8 (labelAt 57 (by decide))
      else .store 8 4 ⟨58 * (index.val + 1), by have i := index.isLt; omega⟩
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
