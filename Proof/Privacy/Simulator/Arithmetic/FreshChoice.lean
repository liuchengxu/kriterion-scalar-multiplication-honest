import Construction.Simulator.FreshChoice
import Proof.Privacy.Simulator.Arithmetic.OracleScratch
import Proof.Privacy.Simulator.Arithmetic.RuntimeSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The fresh block contains the complete runtime sampler before its return. -/
theorem freshChoice_sampler (attempts : Nat) :
    ContainsRuntimeSampler (freshChoice attempts) attempts freshSamplerLabels := by
  intro pc inside
  have bound : pc.val < 31 := inside
  simp [freshChoice, freshSamplerLabels, show 15 ≤ pc.val + 15 by omega,
    show pc.val + 15 < 46 by omega]
  rfl

/-- The fresh block contains the metadata save instructions. -/
theorem freshChoice_save (attempts : Nat) : ContainsLinear (freshChoice attempts) oracleSave
    (fun index => ⟨min index 14, by change min index 14 < 67; omega⟩) := by
  intro index valid
  have bound : index < 14 := valid
  interval_cases index <;> simp [freshChoice, oracleSave, LinearInstruction.emit]

/-- The fresh block contains the metadata restore instructions. -/
theorem freshChoice_restore (attempts : Nat) : ContainsLinear (freshChoice attempts) oracleRestore
    (fun index => ⟨46 + min index 16, by change 46 + min index 16 < 67; omega⟩) := by
  intro index valid
  have bound : index < 16 := valid
  interval_cases index <;> simp [freshChoice, oracleRestore, LinearInstruction.emit]

/-- The fresh block samples from the unused suffix size. -/
def freshChoiceInitial (memory : Memory) : Memory :=
  { oracleSaved memory with registers := Function.update (oracleSaved memory).registers 5 (memory.registers 5 - memory.registers 0) }

/-- The successful branch retains the chosen position in a register and scratch RAM. -/
def freshChoiceFinal (memory : Memory) : Memory :=
  let restored := oracleRestored memory
  if memory.registers 7 = 0#256 then restored
  else
    let chosen := restored.registers 9 + restored.registers 0
    { restored with
      registers := Function.update (Function.update restored.registers 9 chosen) 15 7
      ram := Function.update restored.ram 7 chosen }

/-- The final branch charges the restore block and its selected path. -/
def freshChoiceTailCost (memory : Memory) : Nat :=
  if memory.registers 7 = 0#256 then 18 else 21

/-- The fresh block prepares the sampler in fifteen instructions. -/
theorem freshChoice_setup [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    runPrefix (freshChoice attempts) 15 ⟨0, memory⟩ =
      PMF.pure (some (false, ⟨15, freshChoiceInitial memory⟩, 15)) := by
  simp [runPrefix, step, freshChoice, oracleSave, LinearInstruction.emit,
    freshChoiceInitial, oracleSaved, Arithmetic.eval, PMF.pure_map, Function.update_comm]
  rfl

/-- The final branch returns the chosen position or the sampler's failure flag. -/
theorem freshChoice_tail [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (freshChoice attempts) (fuel + 21) ⟨46, memory⟩ =
      PMF.pure (some (⟨66, freshChoiceFinal memory⟩, freshChoiceTailCost memory)) := by
  have restored := oracleRestore_continue (freshChoice attempts)
    (fun index => ⟨46 + min index 16, by change 46 + min index 16 < 67; omega⟩)
    (freshChoice_restore attempts) memory (fuel + 5)
  change run (freshChoice attempts) (16 + (fuel + 5)) ⟨46, memory⟩ = _ at restored
  rw [show fuel + 21 = 16 + (fuel + 5) by omega, restored]
  change (run (freshChoice attempts) (fuel + 5) ⟨62, oracleRestored memory⟩).map _ = _
  by_cases failed : memory.registers 7 = 0#256
  · simp [run, step, freshChoice, oracleRestored, freshChoiceFinal, freshChoiceTailCost,
      failed, PMF.pure_map]
    rfl
  · simp [run, step, freshChoice, oracleRestored, freshChoiceFinal, freshChoiceTailCost,
      failed, Arithmetic.eval, PMF.pure_map, Function.update_comm]
    rfl

/-- The source law retains each retry state and its actual cost. -/
noncomputable def freshChoiceSamples (attempts : Nat) (memory : Memory) : PMF (Memory × Nat) :=
  runtimeSamplerMemory (memory.registers 5 - memory.registers 0) attempts
    {freshChoiceInitial memory with registers := Function.update (freshChoiceInitial memory).registers 4 (BitVec.ofNat 256 attempts)}

/-- The complete fresh block preserves the runtime sampler's memory distribution. -/
theorem freshChoice_run [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (countFits : attempts < 2 ^ 256) :
    run (freshChoice attempts)
      ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts + 39)
      ⟨0, memory⟩ =
      (freshChoiceSamples attempts memory).map fun result =>
        some (⟨66, freshChoiceFinal result.1⟩, result.2 + freshChoiceTailCost result.1 + 16) := by
  let bound := memory.registers 5 - memory.registers 0
  let initial := freshChoiceInitial memory
  let initialized : Memory :=
    {initial with registers := Function.update initial.registers 4 (BitVec.ofNat 256 attempts)}
  have continued := runtimeSamplerBlock_run (freshChoice attempts) bound attempts 21
    freshSamplerLabels (freshChoice_sampler attempts) initial
    (by simp [initial, freshChoiceInitial, bound]) countFits
  rw [show (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts + 39 =
      15 + ((runtimeTrialCost bound + 2) * attempts + 3 + 21) by dsimp [bound]; omega,
    run_after_prefix, freshChoice_setup attempts memory, PMF.pure_bind]
  dsimp only
  change (run (freshChoice attempts) _ ⟨freshSamplerLabels 0, initial⟩).map _ = _
  rw [continued, PMF.map_bind]
  change (runtimeSamplerMemory bound attempts initialized).bind _ =
    (runtimeSamplerMemory bound attempts initialized).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨sampled, cost⟩
  have costBound := runtimeSamplerMemory_cost bound attempts initialized sampled cost supported
  have remaining : 21 ≤ (runtimeTrialCost bound + 2) * attempts + 3 + 21 - (cost + 1) := by omega
  rw [show (runtimeTrialCost bound + 2) * attempts + 3 + 21 - (cost + 1) =
      ((runtimeTrialCost bound + 2) * attempts + 3 + 21 - (cost + 1) - 21) + 21 by omega]
  change ((run (freshChoice attempts) (_ + 21) ⟨46, sampled⟩).map _).map _ = _
  rw [freshChoice_tail, PMF.pure_map, PMF.pure_map]
  simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [show 1 + (15 + freshChoiceTailCost sampled) = 16 + freshChoiceTailCost sampled by omega]

/-- The fresh block includes all sixty-seven table entries in its charge. -/
theorem freshChoice_budget (attempts : Nat) (memory : Memory) :
    (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts + 39 +
      (freshChoice attempts).size + 1 ≤ 2574 * attempts + 106 := by
  have trial := runtimeTrialCost_bound (memory.registers 5 - memory.registers 0)
  have product := Nat.mul_le_mul_right attempts (show
    runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2 ≤ 2574 by omega)
  change _ + 39 + 66 + 1 ≤ _
  omega

/-- The observer distinguishes a failed draw from every possible chosen position. -/
def freshChoiceValue (memory : Memory) : Option Word :=
  if memory.registers 7 = 0#256 then none else some (memory.registers 9)

/-- Every sampled path restores the original used count before adding the sampled rank. -/
theorem freshChoice_value (attempts : Nat) (original sampled : Memory) (cost : Nat)
    (supported : (sampled, cost) ∈ (freshChoiceSamples attempts original).support) :
    freshChoiceValue (freshChoiceFinal sampled) =
      (trialValue sampled).map (fun rank => rank + original.registers 0) := by
  have unchanged := (runtimeSamplerMemory_data _ _ _ sampled cost supported).2
  have used : sampled.ram 0#256 = original.registers 0 := by
    rw [unchanged]
    simp [freshChoiceInitial, oracleSaved]
  by_cases failed : sampled.registers 7 = 0#256
  · simp [freshChoiceValue, freshChoiceFinal, oracleRestored, trialValue, failed]
  · simp [freshChoiceValue, freshChoiceFinal, oracleRestored, trialValue, failed, used]

/-- The sampled memory law gives the exact cutoff distribution over unused positions. -/
theorem freshChoiceSamples_source [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    (freshChoiceSamples attempts memory).map (fun result => freshChoiceValue (freshChoiceFinal result.1)) =
      (Security.BoundedIntegerSampling.cutoff
        (runtimeRange (memory.registers 5 - memory.registers 0)) attempts).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val + memory.registers 0) := by
  have projected := runtimeSamplerMemory_source
    (memory.registers 5 - memory.registers 0) attempts
    {freshChoiceInitial memory with registers := Function.update (freshChoiceInitial memory).registers 4 (BitVec.ofNat 256 attempts)}
  change (freshChoiceSamples attempts memory).map (fun result => trialValue result.1) = _ at projected
  have values : (freshChoiceSamples attempts memory).map
      (fun result => freshChoiceValue (freshChoiceFinal result.1)) =
      ((freshChoiceSamples attempts memory).map (fun result => trialValue result.1)).map
        (Option.map fun rank => rank + memory.registers 0) := by
    rw [PMF.map_comp]
    change (freshChoiceSamples attempts memory).bind _ = (freshChoiceSamples attempts memory).bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    dsimp only [Function.comp_def]
    rw [freshChoice_value attempts memory result.1 result.2 supported]
  rw [values, projected, PMF.map_comp]
  simp [Function.comp_def, Option.map_map]

/-- The complete machine selects the exact bounded-retry unused-position law. -/
theorem freshChoice_source [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (countFits : attempts < 2 ^ 256) :
    (run (freshChoice attempts)
      ((runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts + 39)
      ⟨0, memory⟩).map (fun result => result.bind fun final => freshChoiceValue final.1.memory) =
      (Security.BoundedIntegerSampling.cutoff
        (runtimeRange (memory.registers 5 - memory.registers 0)) attempts).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val + memory.registers 0) := by
  rw [freshChoice_run attempts memory countFits]
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_some] using
    freshChoiceSamples_source attempts memory

end Kriterion.ArgoMAC.ArithmeticSimulator
