import Construction.Simulator.PointSampler
import Proof.Privacy.Simulator.Arithmetic.ScalarMulBlock
import Proof.Privacy.Simulator.Arithmetic.PointSamplerSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The point sampler contains the complete runtime integer sampler. -/
theorem pointSampler_retry (attempts : Nat) :
    ContainsRuntimeSampler (pointSampler attempts) attempts pointSamplerRetryLabels := by
  intro pc inside
  have positive : 0 < pc.val + 1 := by omega
  have upper : pc.val + 1 < 32 := by omega
  simp [pointSampler, pointSamplerRetryLabels, upper]
  split
  · rfl
  · rename_i impossible
    exact (impossible (by change 0 < pc.val + 1; exact positive)).elim

/-- The point sampler contains the complete scalar multiplication block. -/
theorem pointSampler_multiplication (attempts : Nat) :
    ContainsScalarMul (pointSampler attempts) pointSamplerMulLabels := by
  intro pc inside
  have beyond : ¬(0 < pc.val + 37 ∧ pc.val + 37 < 32) := by omega
  have lower : 37 ≤ pc.val + 37 := by omega
  have upper : pc.val + 37 < 47 := by omega
  simp [pointSampler, pointSamplerMulLabels, beyond, lower, upper]
  rfl

/-- The preparation writes a zero fallback and the standard generator coordinates. -/
def pointPrepared (base : Memory) : Memory :=
  let scalar := if base.registers 7 = 0#256 then Function.update base.registers 0 0 else base.registers
  {base with registers := Function.update (Function.update (Function.update scalar 5 1) 6 1) 7 2}

/-- The fallback uses one additional instruction after the flag branch. -/
def pointPreparationCost (base : Memory) : Nat := if base.registers 7 = 0#256 then 5 else 4

/-- The preparation reads the sampler flag and initializes scalar multiplication. -/
theorem pointSampler_prepare [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    run (pointSampler attempts) (fuel + pointPreparationCost base) ⟨32, base⟩ =
      (run (pointSampler attempts) fuel ⟨37, pointPrepared base⟩).map
        (Option.map fun result => (result.1, result.2 + pointPreparationCost base)) := by
  by_cases zero : base.registers 7 = 0#256
  · simp [pointPreparationCost, pointPrepared, zero, run, step, pointSampler,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
    rfl
  · simp [pointPreparationCost, pointPrepared, zero, run, step, pointSampler,
      PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
    rfl

/-- The preparation gives the accepted scalar or the explicit zero fallback. -/
theorem pointPrepared_scalar (base : Memory) :
    (pointPrepared base).registers 0 = (trialValue base).getD 0 := by
  by_cases zero : base.registers 7 = 0#256 <;> simp [pointPrepared, trialValue, zero]

/-- The preparation gives the exact standard generator. -/
theorem pointPrepared_generator [BN254.FieldCertificate] (base : Memory) :
    readPoint (pointPrepared base).registers scalarMultiple = some Security.standardGenerator := by
  have one : (1 : Word).toNat < BN254.baseFieldModulus := by decide
  have two : (2 : Word).toNat < BN254.baseFieldModulus := by decide
  simp only [readPoint, pointPrepared, scalarMultiple, Function.update_self,
    Function.update_of_ne (by decide : (5 : Register) ≠ 7),
    Function.update_of_ne (by decide : (5 : Register) ≠ 6),
    Function.update_of_ne (by decide : (6 : Register) ≠ 7)]
  simp only [show (1 : Word) ≠ 0 from by decide, if_false, one, two, and_self, if_true]
  exact decodePoint_coordinates 1 2 _

/-- The point sampler charges its final halt. -/
theorem pointSampler_halt [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    run (pointSampler attempts) (fuel + 1) ⟨47, base⟩ = PMF.pure (some (⟨47, base⟩, 1)) := by
  simp [run, step, pointSampler]

/-- The multiplication returns the exact scalar-generator product for every prepared memory. -/
theorem pointSampler_multiply [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    (run (pointSampler attempts) (fuel + 1542) ⟨37, pointPrepared base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      PMF.pure (some (((trialValue base).getD 0).toNat • Security.standardGenerator)) := by
  let prepared := pointPrepared base
  let cost := scalarLoopCost (prepared.registers 0).toNat + 3
  have bound : cost + 1 ≤ 1542 := scalarMul_instruction_bound (prepared.registers 0)
  have remaining : 1 ≤ fuel + 1542 - cost := by omega
  obtain ⟨final, execution, decoded, _⟩ := scalarMulBlock_run (pointSampler attempts)
    pointSamplerMulLabels (pointSampler_multiplication attempts) (fuel + 1542 - cost)
    prepared Security.standardGenerator (pointPrepared_generator base)
  have total : fuel + 1542 = cost + (fuel + 1542 - cost) := by omega
  rw [total]
  change (run (pointSampler attempts) (cost + (fuel + 1542 - cost))
    ⟨pointSamplerMulLabels 0, prepared⟩).map _ = _
  rw [execution]
  have rest : fuel + 1542 - cost = (fuel + 1542 - cost - 1) + 1 := by omega
  rw [rest]
  change ((run (pointSampler attempts) (_ + 1) ⟨47, final⟩).map _).map _ = _
  rw [pointSampler_halt]
  simp only [PMF.pure_map, Option.map_some, Option.bind_some, decoded]
  rw [pointPrepared_scalar]

/-- The complete tail implements the scalar fallback and the generator multiplication. -/
theorem pointSampler_tail [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory) :
    (run (pointSampler attempts) (fuel + 1547) ⟨32, base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      PMF.pure (some (((trialValue base).getD 0).toNat • Security.standardGenerator)) := by
  have small : pointPreparationCost base ≤ 5 := by unfold pointPreparationCost; split <;> omega
  have remaining : 1542 ≤ fuel + 1547 - pointPreparationCost base := by omega
  have total : fuel + 1547 =
      ((fuel + 1547 - pointPreparationCost base - 1542) + 1542) + pointPreparationCost base := by omega
  rw [total, pointSampler_prepare]
  simpa only [PMF.map_comp, Function.comp_def, Option.bind_map] using
    pointSampler_multiply attempts (fuel + 1547 - pointPreparationCost base - 1542) base

/-- The entry loads the scalar modulus into the runtime-range register. -/
def pointSamplerInitialized (base : Memory) : Memory :=
  {base with registers := Function.update base.registers 5 (BitVec.ofNat 256 BN254.scalarFieldModulus)}

/-- This budget includes the bounded sampler, the fallback, and the scalar multiplication. -/
def pointSamplerFuel (attempts : Nat) : Nat :=
  (runtimeTrialCost (BitVec.ofNat 256 BN254.scalarFieldModulus) + 2) * attempts + 1551

/-- The composed machine returns the point computed from its exact sampled memory law. -/
theorem pointSampler_memory [BN254.FieldCertificate] (attempts : Nat) (base : Memory)
    (countFits : attempts < 2 ^ 256) :
    (run (pointSampler attempts) (pointSamplerFuel attempts) ⟨0, base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      (runtimeSamplerMemory (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts
        {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)}).map
        (fun result => some (((trialValue result.1).getD 0).toNat • Security.standardGenerator)) := by
  let bound := BitVec.ofNat 256 BN254.scalarFieldModulus
  let reserved := (runtimeTrialCost bound + 2) * attempts + 3
  let initialized := pointSamplerInitialized base
  let counted : Memory := {initialized with registers := Function.update initialized.registers 4 (BitVec.ofNat 256 attempts)}
  have entry : step (pointSampler attempts) ⟨0, base⟩ = PMF.pure (some (false, ⟨1, initialized⟩)) := by
    simp [step, pointSampler, initialized, pointSamplerInitialized]
    rfl
  have continued := runtimeSamplerBlock_run (pointSampler attempts) bound attempts 1547
    pointSamplerRetryLabels (pointSampler_retry attempts) initialized
    (by simp [initialized, pointSamplerInitialized, bound]) countFits
  have total : pointSamplerFuel attempts = (reserved + 1547) + 1 := by
    dsimp [pointSamplerFuel, reserved, bound]
  rw [total, run, entry, PMF.pure_bind]
  change (((run (pointSampler attempts) (reserved + 1547)
    ⟨pointSamplerRetryLabels 0, initialized⟩).map _).map _) = _
  rw [continued]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.bind_map]
  change (runtimeSamplerMemory bound attempts counted).bind _ = (runtimeSamplerMemory bound attempts counted).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := runtimeSamplerMemory_cost bound attempts counted memory cost supported
  have remaining : 1547 ≤ (runtimeTrialCost bound + 2) * attempts + 3 + 1547 - (cost + 1) := by omega
  have rest : (runtimeTrialCost bound + 2) * attempts + 3 + 1547 - (cost + 1) =
      ((runtimeTrialCost bound + 2) * attempts + 3 + 1547 - (cost + 1) - 1547) + 1547 := by omega
  rw [rest]
  change (run (pointSampler attempts) (_ + 1547) ⟨32, memory⟩).map _ = _
  exact pointSampler_tail attempts _ memory

/-- The composed machine matches the source point sampler with its total zero fallback. -/
theorem pointSampler_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) (countFits : attempts < 2 ^ 256) :
    (run (pointSampler attempts) (pointSamplerFuel attempts) ⟨0, base⟩).map
      (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator) =
      (Security.SimulatorSampling.point.total attempts).law.map some := by
  rw [pointSampler_memory attempts base countFits]
  have projected := congrArg (PMF.map some)
    (pointSamplerMemory_source attempts
      {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)})
  simpa only [PMF.map_comp, Function.comp_def] using projected

/-- The machine retains the uniform point mass with one bounded-draw loss. -/
theorem pointSampler_totalLaw [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) (countFits : attempts < 2 ^ 256) :
    Security.SimulatorMachine.TotalLaw attempts 1
      ((PMF.uniformOfFintype BN254.Point).map some)
      ((run (pointSampler attempts) (pointSamplerFuel attempts) ⟨0, base⟩).map
        (fun result => result.bind fun final => readPoint final.1.memory.registers scalarAccumulator)) := by
  rw [pointSampler_source attempts base countFits]
  have law := (Security.SimulatorSampling.Code.total_law attempts Security.SimulatorSampling.point).map some
  have uniform : Security.SimulatorSampling.point.law = PMF.uniformOfFintype BN254.Point :=
    Security.SimulatorSampling.point_uniform
  rw [uniform] at law
  exact law

/-- The point sampler charges its full instruction budget and all 48 program-table entries. -/
theorem pointSampler_cost (attempts : Nat) :
    pointSamplerFuel attempts + (pointSampler attempts).size + 1 ≤ 2574 * attempts + 1599 := by
  have bound := runtimeTrialCost_bound (BitVec.ofNat 256 BN254.scalarFieldModulus)
  have product := Nat.mul_le_mul_right attempts (show runtimeTrialCost (BitVec.ofNat 256 BN254.scalarFieldModulus) + 2 ≤ 2574 by omega)
  change pointSamplerFuel attempts + 47 + 1 ≤ _
  unfold pointSamplerFuel
  omega

/-- The default point sampler reserves at most 660543 total cost units. -/
theorem pointSampler_256_cost : pointSamplerFuel 256 + (pointSampler 256).size + 1 ≤ 660543 := by
  exact pointSampler_cost 256

end Kriterion.ArgoMAC.ArithmeticSimulator
