import Construction.Simulator.TotalSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each schedule entry gives a runtime range and a fixed output offset. -/
abbrev DrawSpec := Word × Word

/-- Each batch entry reserves 39 instructions, including its sampler and RAM store. -/
def batchSamplerLabels {count : Nat} (index : Fin count) (pc : Fin 36) : Fin (39 * count + 1) :=
  ⟨39 * index.val + 1 + pc.val, by have i := index.isLt; have p := pc.isLt; omega⟩

/-- The batch stores each sampled word at the base address in register ten plus its index.
The batch uses register eight for its store address.
Each schedule entry appears in the charged instruction table. -/
def samplerBatch {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) : Machine := ⟨39 * count,
  Vector.ofFn (fun pc : Fin (39 * count + 1) =>
    if inside : pc.val < 39 * count then
      let index : Fin count := ⟨pc.val / 39, by omega⟩
      let slot := pc.val % 39
      let labelAt (position : Nat) (bound : position < 39) : Fin (39 * count + 1) :=
        ⟨39 * index.val + position, by have i := index.isLt; omega⟩
      if zero : slot = 0 then .constant 5 plan[index].1 (labelAt 1 (by decide))
      else if sampler : slot < 36 then
        relocate (batchSamplerLabels index)
          ((totalSampler attempts plan[index].2).code[slot - 1]'(by change slot - 1 < 36; omega))
      else if slot = 36 then .constant 8 (BitVec.ofNat 256 index.val) (labelAt 37 (by decide))
      else if slot = 37 then .arithmetic .add 8 10 8 (labelAt 38 (by decide))
      else .store 8 0 ⟨39 * (index.val + 1), by have i := index.isLt; omega⟩
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
