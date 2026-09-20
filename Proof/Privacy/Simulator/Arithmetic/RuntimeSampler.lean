import Proof.Privacy.Simulator.Arithmetic.RuntimeSamplerBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone sampler contains its complete body. -/
theorem runtimeSampler_contains (attempts : Nat) :
    ContainsRuntimeSampler (runtimeSampler attempts) attempts id := by
  intro pc inside
  change (runtimeSampler attempts).code[pc.val] = relocate id ((runtimeSampler attempts).code[pc.val])
  generalize (runtimeSampler attempts).code[pc.val] = instruction
  cases instruction <;> rfl

/-- The standalone sampler halts in one instruction. -/
theorem runtimeSampler_tail [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    run (runtimeSampler attempts) (fuel + 1) ⟨31, base⟩ = PMF.pure (some (⟨31, base⟩, 1)) := by
  simp [run, step, runtimeSampler]

/-- The standalone sampler retains its complete memory and actual instruction cost. -/
theorem runtimeSampler_run [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (runtimeSampler attempts) ((runtimeTrialCost (base.registers 5) + 2) * attempts + 4) ⟨0, base⟩ =
      (runtimeSamplerMemory (base.registers 5) attempts
        {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}).map fun result =>
          some (⟨31, result.1⟩, result.2 + 2) := by
  let bound := base.registers 5
  let initialized : Memory := {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}
  have continued := runtimeSamplerBlock_run (runtimeSampler attempts) bound attempts 1 id
    (runtimeSampler_contains attempts) base rfl countFits
  rw [show (runtimeTrialCost (base.registers 5) + 2) * attempts + 4 =
    (runtimeTrialCost bound + 2) * attempts + 3 + 1 by dsimp [bound]]
  simp only [id_eq] at continued
  apply continued.trans
  change (runtimeSamplerMemory bound attempts initialized).bind _ =
    (runtimeSamplerMemory bound attempts initialized).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have costBound := runtimeSamplerMemory_cost bound attempts initialized memory cost supported
  have remaining : 1 ≤ (runtimeTrialCost bound + 2) * attempts + 3 + 1 - (cost + 1) := by omega
  rw [show (runtimeTrialCost bound + 2) * attempts + 3 + 1 - (cost + 1) =
    ((runtimeTrialCost bound + 2) * attempts + 3 + 1 - (cost + 1) - 1) + 1 by omega]
  change (run (runtimeSampler attempts) (_ + 1) ⟨31, memory⟩).map _ = _
  rw [runtimeSampler_tail]
  simp only [PMF.pure_map, Option.map_some, Function.comp_def, show 1 + cost + 1 = cost + 2 by omega]

/-- The runtime sampler matches the source cutoff, including its failure outcome. -/
theorem runtimeSampler_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    (run (runtimeSampler attempts) ((runtimeTrialCost (base.registers 5) + 2) * attempts + 4) ⟨0, base⟩).map
      (fun result => result.bind fun final => trialValue final.1.memory) =
      (Security.BoundedIntegerSampling.cutoff (runtimeRange (base.registers 5)) attempts).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  rw [runtimeSampler_run attempts base countFits]
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_some] using
    runtimeSamplerMemory_source (base.registers 5) attempts
      {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}

/-- The sampler charges its runtime work and all 32 program-table entries. -/
theorem runtimeSampler_cost (bound : Word) (attempts : Nat) :
    (runtimeTrialCost bound + 2) * attempts + 4 + (runtimeSampler attempts).size + 1 ≤
      2574 * attempts + 36 := by
  have product := Nat.mul_le_mul_right attempts
    (show runtimeTrialCost bound + 2 ≤ 2574 by have h := runtimeTrialCost_bound bound; omega)
  change _ + 4 + 31 + 1 ≤ _
  omega

/-- The default retry limit uses at most 658980 total cost units. -/
theorem runtimeSampler_256_cost (bound : Word) :
    (runtimeTrialCost bound + 2) * 256 + 4 + (runtimeSampler 256).size + 1 ≤ 658980 := by
  exact runtimeSampler_cost bound 256

/-- The runtime machine has the exact geometric failure probability of the source cutoff. -/
theorem runtimeSampler_failure [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    ((run (runtimeSampler attempts) ((runtimeTrialCost (base.registers 5) + 2) * attempts + 4) ⟨0, base⟩).map
      (fun result => result.bind fun final => trialValue final.1.memory)) none =
      Security.BoundedIntegerSampling.rejection (runtimeRange (base.registers 5)) ^ attempts := by
  rw [runtimeSampler_source attempts base countFits, PMF.map_apply]
  have accepts : ∀ value : Option (Fin (runtimeRange (base.registers 5))),
      (none : Option Word) = value.map (fun accepted => BitVec.ofNat 256 accepted.val) ↔ value = none := by
    intro value
    cases value <;> simp
  simp_rw [accepts]
  rw [tsum_ite_eq]
  exact Security.BoundedIntegerSampling.cutoff_none (runtimeRange (base.registers 5)) attempts

/-- The default runtime sampler fails with probability at most two to the minus 256. -/
theorem runtimeSampler_256_failure [BN254.FieldCertificate] (base : Memory) :
    ((run (runtimeSampler 256) ((runtimeTrialCost (base.registers 5) + 2) * 256 + 4) ⟨0, base⟩).map
      (fun result => result.bind fun final => trialValue final.1.memory)) none ≤ (2 : ENNReal)⁻¹ ^ 256 := by
  rw [runtimeSampler_failure 256 base (by decide)]
  exact pow_le_pow_left₀ (by positivity)
    (Security.BoundedIntegerSampling.rejection_le_half (runtimeRange (base.registers 5))
      (runtimeRange_bounds _).1) 256

end Kriterion.ArgoMAC.ArithmeticSimulator
