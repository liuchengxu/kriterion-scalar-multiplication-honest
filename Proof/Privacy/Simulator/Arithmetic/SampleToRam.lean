import Construction.Simulator.SampleToRam
import Proof.Privacy.Simulator.Arithmetic.SamplerBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The storage program contains the complete sampler before its store instruction. -/
theorem sampleToRam_contains (size attempts : Nat) :
    ContainsSampler (sampleToRam size attempts) size attempts storageLabels := by
  intro pc inside
  simp [sampleToRam, storageLabels, inside]
  rfl

/-- The caller stores the word and halts in two instructions. -/
theorem sampleToRam_tail [BN254.FieldCertificate] (size attempts fuel : Nat) (base : Memory) :
    run (sampleToRam size attempts) (fuel + 2) ⟨24, base⟩ =
      PMF.pure (some (⟨25, {base with ram := Function.update base.ram (base.registers 8) (base.registers 0)}⟩, 2)) := by
  simp [run, step, sampleToRam, PMF.pure_map]
  rfl

/-- The actual caller resumes after the sampler and writes to its saved RAM address. -/
theorem sampleToRam_run [BN254.FieldCertificate] (size attempts : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    run (sampleToRam size attempts) ((trialCost size + 2) * attempts + 5) ⟨0, base⟩ =
      (samplerMemory size attempts
        {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}).map fun result =>
          some (⟨25, {result.1 with ram := Function.update base.ram (base.registers 8) (result.1.registers 0)}⟩,
            result.2 + 3) := by
  let initialized : Memory := {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}
  have continued := samplerBlock_run (sampleToRam size attempts) size attempts 2 storageLabels
    (sampleToRam_contains size attempts) base positive bounded countFits
  rw [show (trialCost size + 2) * attempts + 5 = (trialCost size + 2) * attempts + 3 + 2 by omega]
  change run (sampleToRam size attempts) ((trialCost size + 2) * attempts + 3 + 2)
    ⟨storageLabels 0, base⟩ = _
  rw [continued]
  change (samplerMemory size attempts initialized).bind _ = (samplerMemory size attempts initialized).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have costBound := samplerMemory_cost size attempts initialized memory cost supported
  have retained := samplerMemory_data size attempts initialized memory cost supported
  have address := samplerMemory_caller size attempts initialized memory cost 8 (by decide) supported
  dsimp only [initialized] at retained address
  rw [Function.update_of_ne (by decide : (8 : Register) ≠ 4)] at address
  have remaining : 2 ≤ (trialCost size + 2) * attempts + 3 + 2 - (cost + 1) := by omega
  rw [show (trialCost size + 2) * attempts + 3 + 2 - (cost + 1) =
    ((trialCost size + 2) * attempts + 3 + 2 - (cost + 1) - 2) + 2 by omega]
  change (run (sampleToRam size attempts) (_ + 2) ⟨24, memory⟩).map _ = _
  rw [sampleToRam_tail]
  simp only [PMF.pure_map, Option.map_some]
  rw [retained.2, address]
  simp only [Function.comp_def, show 2 + cost + 1 = cost + 3 by omega]

/-- Reading the stored word and its flag gives the source cutoff law. -/
theorem sampleToRam_source [BN254.FieldCertificate] (size attempts : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) (countFits : attempts < 2 ^ 256) :
    (run (sampleToRam size attempts) ((trialCost size + 2) * attempts + 5) ⟨0, base⟩).map
      (fun result => result.bind fun final =>
        if final.1.memory.registers 7 = 0 then none else some (final.1.memory.ram (base.registers 8))) =
      (Security.BoundedIntegerSampling.cutoff size attempts).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  rw [sampleToRam_run size attempts base positive bounded countFits, PMF.map_comp]
  simp only [Function.comp_def, Option.bind_some, Function.update_self]
  have source := samplerMemory_source size attempts
    {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)} positive bounded
  have projected := congrArg (PMF.map Prod.fst) source
  rw [retryLaw_source] at projected
  simpa only [PMF.map_comp, Function.comp_def, trialValue] using projected

/-- The storage caller charges one store instruction and all program-table entries. -/
theorem sampleToRam_cost (size attempts : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (trialCost size + 2) * attempts + 5 + ((sampleToRam size attempts).size + 1) ≤
      1804 * attempts + 31 := by
  have bound := (boundedTrial_cost size positive bounded).1
  have product := Nat.mul_le_mul_right attempts (show trialCost size + 2 ≤ 1804 by omega)
  have table : (sampleToRam size attempts).size + 1 = 26 := rfl
  omega

/-- The default storage caller reserves at most 461855 total units. -/
theorem sampleToRam_256_cost (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (trialCost size + 2) * 256 + 5 + ((sampleToRam size 256).size + 1) ≤ 461855 := by
  exact sampleToRam_cost size 256 positive bounded

end Kriterion.ArgoMAC.ArithmeticSimulator
