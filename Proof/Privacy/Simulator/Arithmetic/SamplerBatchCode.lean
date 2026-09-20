import Construction.Simulator.SamplerBatch
import Proof.Privacy.Simulator.Arithmetic.PrivateSamplers

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The batch contains the complete total sampler for each schedule entry. -/
theorem samplerBatch_contains {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) (index : Fin count) :
    ContainsTotalSampler (samplerBatch plan attempts fits) attempts plan[index].2 (batchSamplerLabels index) := by
  intro pc inside
  have i := index.isLt
  have p := pc.isLt
  have position : 39 * index.val + 1 + pc.val < 39 * count := by omega
  have quotient : (39 * index.val + 1 + pc.val) / 39 = index.val := by omega
  have remainder : (39 * index.val + 1 + pc.val) % 39 = pc.val + 1 := by omega
  have nonzero : pc.val + 1 ≠ 0 := by omega
  have bound : pc.val + 1 < 36 := by omega
  simp only [samplerBatch, batchSamplerLabels, Vector.getElem_ofFn, position, dif_pos, quotient, remainder,
    nonzero, if_false, bound, if_true, Nat.add_sub_cancel]
  rw [dif_neg (fun impossible : False => impossible)]
  have selected : (⟨(39 * index.val + 1 + pc.val) / 39, by omega⟩ : Fin count) = index := Fin.ext quotient
  exact congrArg (fun item : Fin count => relocate (batchSamplerLabels index)
    ((totalSampler attempts plan[item].2).code[pc.val]'(by exact pc.isLt))) selected

/-- The batch entry loads the selected runtime range. -/
theorem samplerBatch_entry_code {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) (index : Fin count) :
    (samplerBatch plan attempts fits).code[39 * index.val]'(by change 39 * index.val < 39 * count + 1; have h := index.isLt; omega) =
      .constant 5 plan[index].1 (batchSamplerLabels index 0) := by
  have i := index.isLt
  have position : 39 * index.val < 39 * count := by omega
  have quotient : 39 * index.val / 39 = index.val := by omega
  have remainder : 39 * index.val % 39 = 0 := by omega
  simp [samplerBatch, batchSamplerLabels, position, quotient, remainder]

/-- The batch store tail writes the exact sampled word to its indexed address. -/
theorem samplerBatch_store [BN254.FieldCertificate] {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) (index : Fin count) (fuel : Nat) (base : Memory) :
    run (samplerBatch plan attempts fits) (fuel + 3) ⟨batchSamplerLabels index 35, base⟩ =
      (run (samplerBatch plan attempts fits) fuel
        ⟨⟨39 * (index.val + 1), by change 39 * (index.val + 1) < 39 * count + 1; have h := index.isLt; omega⟩,
          {base with
            registers := Function.update base.registers 8 (base.registers 10 + BitVec.ofNat 256 index.val)
            ram := Function.update base.ram (base.registers 10 + BitVec.ofNat 256 index.val) (base.registers 0)}⟩).map
        (Option.map fun result => (result.1, result.2 + 3)) := by
  have i := index.isLt
  have p36 : 39 * index.val + 36 < 39 * count := by omega
  have p37 : 39 * index.val + 37 < 39 * count := by omega
  have p38 : 39 * index.val + 38 < 39 * count := by omega
  have q36 : (39 * index.val + 36) / 39 = index.val := by omega
  have q37 : (39 * index.val + 37) / 39 = index.val := by omega
  have q38 : (39 * index.val + 38) / 39 = index.val := by omega
  have r36 : (39 * index.val + 36) % 39 = 36 := by omega
  have r37 : (39 * index.val + 37) % 39 = 37 := by omega
  have r38 : (39 * index.val + 38) % 39 = 38 := by omega
  simp [run, step, samplerBatch, batchSamplerLabels,
    show 39 * index.val + 1 + 35 = 39 * index.val + 36 by omega,
    p36, p37, p38, q36, q37, q38, r36, r37, r38, Arithmetic.eval,
    PMF.map_comp, Option.map_map, Function.comp_def, Function.update_comm, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
