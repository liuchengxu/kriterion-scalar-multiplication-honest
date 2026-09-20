import Proof.Privacy.Simulator.Arithmetic.TotalSamplerMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone total sampler contains its complete body. -/
theorem totalSampler_contains (attempts : Nat) (offset : Word) :
    ContainsTotalSampler (totalSampler attempts offset) attempts offset id := by
  intro pc inside
  change (totalSampler attempts offset).code[pc.val] =
    relocate id ((totalSampler attempts offset).code[pc.val])
  generalize (totalSampler attempts offset).code[pc.val] = instruction
  cases instruction <;> rfl

/-- The total sampler charges its final halt. -/
theorem totalSampler_halt [BN254.FieldCertificate] (attempts fuel : Nat) (offset : Word) (base : Memory) :
    run (totalSampler attempts offset) (fuel + 1) ⟨35, base⟩ = PMF.pure (some (⟨35, base⟩, 1)) := by
  simp [run, step, totalSampler]

/-- The standalone total sampler returns its exact memory and instruction cost. -/
theorem totalSampler_run [BN254.FieldCertificate] (attempts : Nat) (offset : Word) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (totalSampler attempts offset) ((runtimeTrialCost (base.registers 5) + 2) * attempts + 8) ⟨0, base⟩ =
      (totalSamplerMemory (base.registers 5) attempts offset base).map fun result =>
        some (⟨35, result.1⟩, result.2 + 1) := by
  let bound := base.registers 5
  have continued := totalSamplerBlock_run (totalSampler attempts offset) attempts offset bound id
    (totalSampler_contains attempts offset) 1 base rfl countFits
  rw [show (runtimeTrialCost (base.registers 5) + 2) * attempts + 8 =
    (runtimeTrialCost bound + 2) * attempts + 7 + 1 by dsimp [bound]]
  simp only [id_eq] at continued
  apply continued.trans
  change (totalSamplerMemory bound attempts offset base).bind _ = (totalSamplerMemory bound attempts offset base).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := totalSamplerMemory_cost bound attempts offset base memory cost supported
  have remaining : 1 ≤ (runtimeTrialCost bound + 2) * attempts + 7 + 1 - cost := by omega
  rw [show (runtimeTrialCost bound + 2) * attempts + 7 + 1 - cost =
    ((runtimeTrialCost bound + 2) * attempts + 7 + 1 - cost - 1) + 1 by omega]
  change (run (totalSampler attempts offset) (_ + 1) ⟨35, memory⟩).map _ = _
  rw [totalSampler_halt]
  simp only [PMF.pure_map, Option.map_some, Nat.add_comm]
  rfl

/-- The standalone machine gives the exact total-integer source law and fixed offset. -/
theorem totalSampler_source [BN254.FieldCertificate] (attempts : Nat) (offset : Word) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    (run (totalSampler attempts offset) ((runtimeTrialCost (base.registers 5) + 2) * attempts + 8) ⟨0, base⟩).map
      (Option.map fun final => final.1.memory.registers 0) =
      (Security.BoundedIntegerSampling.totalInteger (runtimeRange (base.registers 5))
        (runtimeRange_bounds (base.registers 5)).1 attempts).law.map
        (fun value => some (BitVec.ofNat 256 value.val + offset)) := by
  rw [totalSampler_run attempts offset base countFits]
  have source := congrArg (PMF.map some) (totalSamplerMemory_source (base.registers 5) attempts offset base)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using source

/-- The total sampler pays for its instruction budget and all 36 table entries. -/
theorem totalSampler_cost (bound offset : Word) (attempts : Nat) :
    (runtimeTrialCost bound + 2) * attempts + 8 + (totalSampler attempts offset).size + 1 ≤
      2574 * attempts + 44 := by
  have product := Nat.mul_le_mul_right attempts
    (show runtimeTrialCost bound + 2 ≤ 2574 by have h := runtimeTrialCost_bound bound; omega)
  change _ + 8 + 35 + 1 ≤ _
  omega

/-- The default total sampler pays at most 658988 units. -/
theorem totalSampler_256_cost (bound offset : Word) :
    (runtimeTrialCost bound + 2) * 256 + 8 + (totalSampler 256 offset).size + 1 ≤ 658988 :=
  totalSampler_cost bound offset 256

end Kriterion.ArgoMAC.ArithmeticSimulator
