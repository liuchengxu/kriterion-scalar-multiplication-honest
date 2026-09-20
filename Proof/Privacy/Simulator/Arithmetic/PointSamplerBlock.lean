import Proof.Privacy.Simulator.Arithmetic.PointSampler
import Proof.Privacy.Simulator.Arithmetic.ScalarMulMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every point-sampler instruction before its return. -/
def ContainsPointSampler (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 48, pc.val < 47 → host.code[(labels pc).val] =
    relocate labels ((pointSampler attempts).code[pc.val]'(by exact pc.isLt))

/-- The host contains the runtime scalar sampler. -/
theorem pointSamplerBlock_retry (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) (present : ContainsPointSampler host attempts labels) :
    ContainsRuntimeSampler host attempts (labels ∘ pointSamplerRetryLabels) := by
  intro pc inside
  have selected := present (pointSamplerRetryLabels pc) (by change pc.val + 1 < 47; omega)
  exact (selected.trans (congrArg (relocate labels) (pointSampler_retry attempts pc inside))).trans
    (relocate_comp pointSamplerRetryLabels labels _)

/-- The host contains the scalar multiplication block. -/
theorem pointSamplerBlock_multiplication (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) (present : ContainsPointSampler host attempts labels) :
    ContainsScalarMul host (labels ∘ pointSamplerMulLabels) := by
  intro pc inside
  have selected := present (pointSamplerMulLabels pc) (by change pc.val + 37 < 47; omega)
  exact (selected.trans (congrArg (relocate labels) (pointSampler_multiplication attempts pc inside))).trans
    (relocate_comp pointSamplerMulLabels labels _)

/-- The embedded preparation writes the exact fallback scalar and the standard generator. -/
theorem pointSamplerBlock_prepare [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) (present : ContainsPointSampler host attempts labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + pointPreparationCost base) ⟨labels 32, base⟩ =
      (run host fuel ⟨labels 37, pointPrepared base⟩).map
        (Option.map fun result => (result.1, result.2 + pointPreparationCost base)) := by
  by_cases zero : base.registers 7 = 0#256 <;>
    simp [run, step, present 32 (by decide), present 33 (by decide), present 34 (by decide),
      present 35 (by decide), present 36 (by decide), pointSampler, relocate,
      pointPreparationCost, pointPrepared, zero, PMF.map_comp, Option.map_map,
      Function.comp_def, Nat.add_assoc]

/-- The final point memory contains the generator multiple after the total scalar fallback. -/
def pointSamplerFinal [BN254.FieldCertificate] (base : Memory) : Memory :=
  scalarFinish (pointPrepared base) Security.standardGenerator

/-- The tail cost includes preparation and scalar multiplication before the host return. -/
def pointSamplerTailCost (base : Memory) : Nat :=
  pointPreparationCost base + (scalarLoopCost ((pointPrepared base).registers 0).toNat + 3)

/-- The complete point tail uses at most 1546 instructions before its return. -/
theorem pointSamplerTailCost_bound (base : Memory) : pointSamplerTailCost base ≤ 1546 := by
  have multiplication := scalarMul_instruction_bound ((pointPrepared base).registers 0)
  have preparation : pointPreparationCost base ≤ 5 := by unfold pointPreparationCost; split <;> omega
  unfold pointSamplerTailCost
  omega

/-- The point tail returns its exact memory and actual prefix cost to the host. -/
theorem pointSamplerBlock_tail [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) (present : ContainsPointSampler host attempts labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + pointSamplerTailCost base) ⟨labels 32, base⟩ =
      (run host fuel ⟨labels 47, pointSamplerFinal base⟩).map
        (Option.map fun result => (result.1, result.2 + pointSamplerTailCost base)) := by
  let cost := scalarLoopCost ((pointPrepared base).registers 0).toNat + 3
  have prepared := pointSamplerBlock_prepare host attempts labels present (cost + fuel) base
  have total : fuel + pointSamplerTailCost base = (cost + fuel) + pointPreparationCost base := by
    dsimp [cost, pointSamplerTailCost]
    omega
  rw [total, prepared]
  have block := scalarMulBlock_memory host (labels ∘ pointSamplerMulLabels)
    (pointSamplerBlock_multiplication host attempts labels present) (pointPrepared base)
    Security.standardGenerator (pointPrepared_generator base)
  have continued := run_after_prefix host cost fuel ⟨(labels ∘ pointSamplerMulLabels) 0, pointPrepared base⟩
  rw [block, PMF.pure_bind] at continued
  change (run host (cost + fuel) ⟨(labels ∘ pointSamplerMulLabels) 0, pointPrepared base⟩).map _ = _
  rw [continued]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  change (run host fuel ⟨labels 47, pointSamplerFinal base⟩).map _ = _
  apply congrArg (fun f => PMF.map f (run host fuel ⟨labels 47, pointSamplerFinal base⟩))
  funext result
  cases result <;> simp [pointSamplerTailCost, cost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The final point memory gives the exact generator multiple and preserves caller data. -/
theorem pointSamplerFinal_spec [BN254.FieldCertificate] (base : Memory) :
    readPoint (pointSamplerFinal base).registers scalarAccumulator =
      some (((trialValue base).getD 0).toNat • Security.standardGenerator) ∧
    (pointSamplerFinal base).bits = base.bits ∧ (pointSamplerFinal base).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val → (pointSamplerFinal base).registers register = base.registers register := by
  obtain ⟨point, bitStore, ram, caller⟩ := scalarFinish_spec (pointPrepared base)
    Security.standardGenerator (pointPrepared_generator base)
  refine ⟨?_, bitStore, ram, ?_⟩
  · simpa only [pointSamplerFinal, pointPrepared_scalar] using point
  · intro register outside
    have different (target : Register) (localRegister : target.val < 9) : register ≠ target := by
      intro equal
      have values := congrArg Fin.val equal
      omega
    dsimp only [pointSamplerFinal]
    rw [caller register outside]
    dsimp only [pointPrepared]
    rw [Function.update_of_ne (different 7 (by decide)), Function.update_of_ne (different 6 (by decide)),
      Function.update_of_ne (different 5 (by decide))]
    split
    · exact Function.update_of_ne (different 0 (by decide)) _ _
    · rfl

/-- This return law records the point memory and every instruction before the host return. -/
noncomputable def pointSamplerReturnMemory [BN254.FieldCertificate] (attempts : Nat) (base : Memory) : PMF (Memory × Nat) :=
  (runtimeSamplerMemory (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts
    {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)}).map
    (fun result => (pointSamplerFinal result.1, result.2 + 2 + pointSamplerTailCost result.1))

/-- Every return cost fits in the fixed point-sampler prefix budget. -/
theorem pointSamplerReturnMemory_cost [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointSamplerReturnMemory attempts base).support) :
    cost ≤ pointSamplerFuel attempts - 1 := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have bounded := runtimeSamplerMemory_cost (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts _ memory spent member
  have tail := pointSamplerTailCost_bound memory
  dsimp only
  unfold pointSamplerFuel
  omega

/-- The host resumes after the complete point sampler with its exact memory and unused fuel. -/
theorem pointSamplerBlock_run [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 48 → Fin (host.size + 1)) (present : ContainsPointSampler host attempts labels)
    (fuel : Nat) (base : Memory) (countFits : attempts < 2 ^ 256) :
    run host (pointSamplerFuel attempts - 1 + fuel) ⟨labels 0, base⟩ =
      (pointSamplerReturnMemory attempts base).bind fun result =>
        (run host (pointSamplerFuel attempts - 1 + fuel - result.2) ⟨labels 47, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  let bound := BitVec.ofNat 256 BN254.scalarFieldModulus
  let initialized := pointSamplerInitialized base
  have entry : step host ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 1, initialized⟩)) := by
    simp [step, present 0 (by decide), pointSampler, relocate, initialized, pointSamplerInitialized]
  have continued := runtimeSamplerBlock_run host bound attempts (1546 + fuel)
    (labels ∘ pointSamplerRetryLabels) (pointSamplerBlock_retry host attempts labels present) initialized
    (by simp [initialized, pointSamplerInitialized, bound]) countFits
  have total : pointSamplerFuel attempts - 1 + fuel =
      ((runtimeTrialCost bound + 2) * attempts + 3 + (1546 + fuel)) + 1 := by
    dsimp [pointSamplerFuel, bound]
    omega
  rw [total, run, entry, PMF.pure_bind]
  change (run host ((runtimeTrialCost bound + 2) * attempts + 3 + (1546 + fuel))
    ⟨(labels ∘ pointSamplerRetryLabels) 0, initialized⟩).map _ = _
  rw [continued, PMF.map_bind, pointSamplerReturnMemory, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := runtimeSamplerMemory_cost bound attempts _ memory cost supported
  have tail := pointSamplerTailCost_bound memory
  have amount : (runtimeTrialCost bound + 2) * attempts + 3 + (1546 + fuel) - (cost + 1) =
      (((runtimeTrialCost bound + 2) * attempts + 3 + (1546 + fuel) + 1) -
        (cost + 2 + pointSamplerTailCost memory)) + pointSamplerTailCost memory := by omega
  rw [amount]
  change ((run host (_ + pointSamplerTailCost memory) ⟨labels 32, memory⟩).map _).map _ = _
  rw [pointSamplerBlock_tail host attempts labels present]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  apply congrArg (fun f => PMF.map f
    (run host (((runtimeTrialCost bound + 2) * attempts + 3 + (1546 + fuel) + 1) -
      (cost + 2 + pointSamplerTailCost memory)) ⟨labels 47, pointSamplerFinal memory⟩))
  funext outcome
  cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- The point return law gives the exact source point distribution. -/
theorem pointSamplerReturnMemory_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) :
    (pointSamplerReturnMemory attempts base).map (fun result => readPoint result.1.registers scalarAccumulator) =
      (Security.SimulatorSampling.point.total attempts).law.map some := by
  simp only [pointSamplerReturnMemory, PMF.map_comp, Function.comp_def, (pointSamplerFinal_spec _).1]
  have source := congrArg (PMF.map some)
    (pointSamplerMemory_source attempts
      {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)})
  simpa only [PMF.map_comp, Function.comp_def] using source

/-- The point return law preserves the caller's stacks and RAM. -/
theorem pointSamplerReturnMemory_data [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointSamplerReturnMemory attempts base).support) :
    final.bits = base.bits ∧ final.ram = base.ram := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have retained := runtimeSamplerMemory_data (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts
    {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)}
    memory spent member
  have final := pointSamplerFinal_spec memory
  exact ⟨final.2.1.trans retained.1, final.2.2.1.trans retained.2⟩

/-- The point return law preserves registers nine through fifteen. -/
theorem pointSamplerReturnMemory_caller [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 9 ≤ register.val)
    (supported : (final, cost) ∈ (pointSamplerReturnMemory attempts base).support) :
    final.registers register = base.registers register := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have retained := runtimeSamplerMemory_caller (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts
    {pointSamplerInitialized base with registers := Function.update (pointSamplerInitialized base).registers 4 (BitVec.ofNat 256 attempts)}
    memory spent register (by omega) member
  have different (target : Register) (localRegister : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  have final := (pointSamplerFinal_spec memory).2.2.2 register caller
  rw [final, retained]
  dsimp only [pointSamplerInitialized]
  rw [Function.update_of_ne (different 4 (by decide)), Function.update_of_ne (different 5 (by decide))]

end Kriterion.ArgoMAC.ArithmeticSimulator
