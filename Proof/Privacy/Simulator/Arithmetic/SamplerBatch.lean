import Proof.Privacy.Simulator.Arithmetic.SamplerBatchBlock
import Proof.Privacy.Simulator.Arithmetic.SamplerBatchSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone batch contains all its instructions before the final halt. -/
theorem samplerBatch_self {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) :
    ContainsSamplerBatch (samplerBatch plan attempts fits) plan attempts fits id := by
  intro pc inside
  change (samplerBatch plan attempts fits).code[pc.val] =
    relocate id ((samplerBatch plan attempts fits).code[pc.val])
  generalize (samplerBatch plan attempts fits).code[pc.val] = instruction
  cases instruction <;> rfl

/-- The standalone batch charges its final halt. -/
theorem samplerBatch_halt [BN254.FieldCertificate] {count : Nat} (plan : Vector DrawSpec count)
    (attempts fuel : Nat) (fits : 39 * count < 2 ^ 256) (base : Memory) :
    run (samplerBatch plan attempts fits) (fuel + 1) ⟨batchBoundary count (Nat.le_refl count), base⟩ =
      PMF.pure (some (⟨batchBoundary count (Nat.le_refl count), base⟩, 1)) := by
  simp [run, step, samplerBatch, batchBoundary]

/-- The complete machine returns the exact memory law and charges its halt. -/
theorem samplerBatch_run [BN254.FieldCertificate] {count : Nat} (plan : Vector DrawSpec count)
    (attempts : Nat) (fits : 39 * count < 2 ^ 256) (base : Memory) (countFits : attempts < 2 ^ 256) :
    run (samplerBatch plan attempts fits) (batchStepBudget attempts * count + 1) ⟨0, base⟩ =
      (samplerBatchMemory plan attempts count 0 base).map fun result =>
        some (⟨batchBoundary count (Nat.le_refl count), result.1⟩, result.2 + 1) := by
  have continued := samplerBatchBlock_run (samplerBatch plan attempts fits) plan attempts fits id
    (samplerBatch_self plan attempts fits) count 0 1 base (by omega) countFits
  simp only [id_eq, Nat.zero_add] at continued
  apply continued.trans
  change (samplerBatchMemory plan attempts count 0 base).bind _ = (samplerBatchMemory plan attempts count 0 base).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := samplerBatchMemory_cost plan attempts count 0 base memory cost supported
  have amount : batchStepBudget attempts * count + 1 - cost =
      (batchStepBudget attempts * count - cost) + 1 := by omega
  rw [amount, samplerBatch_halt]
  simp only [PMF.pure_map, Option.map_some, Nat.add_comm]
  rfl

/-- The instruction budget includes every symbolic table entry. -/
theorem samplerBatch_cost {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat)
    (fits : 39 * count < 2 ^ 256) :
    batchStepBudget attempts * count + 1 + (samplerBatch plan attempts fits).size + 1 =
      (2574 * attempts + 50) * count + 2 := by
  change batchStepBudget attempts * count + 1 + 39 * count + 1 = _
  unfold batchStepBudget
  ring

/-- The offline machine uses the exact fixed source schedule. -/
def offlineSampler (attempts : Nat) : Machine := samplerBatch offlinePlan attempts (by decide)

/-- The offline machine returns the exact total private coin in RAM. -/
theorem offlineSampler_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    (run (offlineSampler attempts) (batchStepBudget attempts * 838208 + 1) ⟨0, base⟩).map
      (Option.map fun result => result.1.memory.ram) =
      (Security.SimulatorSampling.offline.total attempts).law.map
        (fun coin => some (storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin))) := by
  rw [offlineSampler, samplerBatch_run offlinePlan attempts _ base countFits]
  have source := congrArg (PMF.map some) (offlineMemory_source attempts base)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using source

/-- The default offline sampler pays for all instructions and all table entries. -/
theorem offlineSampler_256_cost :
    batchStepBudget 256 * 838208 + 1 + (offlineSampler 256).size + 1 = 552374042754 := by
  rw [offlineSampler, samplerBatch_cost]

end Kriterion.ArgoMAC.ArithmeticSimulator
