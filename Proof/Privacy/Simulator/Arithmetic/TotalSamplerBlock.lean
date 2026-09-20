import Construction.Simulator.TotalSampler
import Proof.Privacy.Simulator.Arithmetic.RuntimeSampler
import Proof.Privacy.Simulator.SimulatorTotalSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every total-sampler instruction before its return. -/
def ContainsTotalSampler (host : Machine) (attempts : Nat) (offset : Word)
    (labels : Fin 36 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 36, pc.val < 35 → host.code[(labels pc).val] =
    relocate labels ((totalSampler attempts offset).code[pc.val]'(by exact pc.isLt))

/-- The host contains the runtime-range sampler. -/
theorem totalSamplerBlock_retry (host : Machine) (attempts : Nat) (offset : Word)
    (labels : Fin 36 → Fin (host.size + 1)) (present : ContainsTotalSampler host attempts offset labels) :
    ContainsRuntimeSampler host attempts (labels ∘ totalSamplerRetryLabels) := by
  intro pc inside
  have selected := present (totalSamplerRetryLabels pc) (by change pc.val < 35; omega)
  have source : (totalSampler attempts offset).code[(totalSamplerRetryLabels pc).val] =
      relocate totalSamplerRetryLabels ((runtimeSampler attempts).code[pc.val]'(by exact pc.isLt)) := by
    simp [totalSampler, totalSamplerRetryLabels, inside]
    rfl
  exact (selected.trans (congrArg (relocate labels) source)).trans
    (relocate_comp totalSamplerRetryLabels labels _)

/-- The total result records the explicit fallback and the fixed offset. -/
def totalSamplerFinal (base : Memory) (offset : Word) : Memory :=
  let fallback := if base.registers 7 = 0#256 then Function.update base.registers 0 0 else base.registers
  let ready := Function.update fallback 6 offset
  {base with registers := Function.update ready 0 (fallback 0 + offset)}

/-- The tail charges one extra instruction when it uses the fallback. -/
def totalSamplerTailCost (base : Memory) : Nat := if base.registers 7 = 0#256 then 4 else 3

/-- The total tail returns before the host instruction and charges every executed instruction. -/
theorem totalSamplerBlock_tail [BN254.FieldCertificate] (host : Machine) (attempts : Nat) (offset : Word)
    (labels : Fin 36 → Fin (host.size + 1)) (present : ContainsTotalSampler host attempts offset labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + totalSamplerTailCost base) ⟨labels 31, base⟩ =
      (run host fuel ⟨labels 35, totalSamplerFinal base offset⟩).map
        (Option.map fun result => (result.1, result.2 + totalSamplerTailCost base)) := by
  by_cases zero : base.registers 7 = 0#256 <;>
    simp [run, step, present 31 (by decide), present 32 (by decide), present 33 (by decide),
      present 34 (by decide), totalSampler, relocate, totalSamplerFinal, totalSamplerTailCost,
      zero, Arithmetic.eval, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The result word equals the accepted value or its zero fallback, plus the fixed offset. -/
theorem totalSamplerFinal_value (base : Memory) (offset : Word) :
    (totalSamplerFinal base offset).registers 0 = (trialValue base).getD 0 + offset := by
  by_cases zero : base.registers 7 = 0#256 <;> simp [totalSamplerFinal, trialValue, zero]

/-- The complete result law retains the exact memory and the prefix cost. -/
noncomputable def totalSamplerMemory (bound : Word) (attempts : Nat) (offset : Word) (base : Memory) :
    PMF (Memory × Nat) :=
  (runtimeSamplerMemory bound attempts
    {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}).map fun result =>
      (totalSamplerFinal result.1 offset, result.2 + 1 + totalSamplerTailCost result.1)

/-- The return law fits within the reserved instruction budget. -/
theorem totalSamplerMemory_cost (bound : Word) (attempts : Nat) (offset : Word)
    (base final : Memory) (cost : Nat) (supported : (final, cost) ∈ (totalSamplerMemory bound attempts offset base).support) :
    cost ≤ (runtimeTrialCost bound + 2) * attempts + 7 := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have bounded := runtimeSamplerMemory_cost bound attempts _ memory spent member
  have tail : totalSamplerTailCost memory ≤ 4 := by unfold totalSamplerTailCost; split <;> omega
  dsimp only
  omega

/-- The host resumes with the exact total-sampler return law and the unused fuel. -/
theorem totalSamplerBlock_run [BN254.FieldCertificate] (host : Machine) (attempts : Nat) (offset bound : Word)
    (labels : Fin 36 → Fin (host.size + 1)) (present : ContainsTotalSampler host attempts offset labels)
    (fuel : Nat) (base : Memory) (range : base.registers 5 = bound) (countFits : attempts < 2 ^ 256) :
    run host ((runtimeTrialCost bound + 2) * attempts + 7 + fuel) ⟨labels 0, base⟩ =
      (totalSamplerMemory bound attempts offset base).bind fun result =>
        (run host ((runtimeTrialCost bound + 2) * attempts + 7 + fuel - result.2) ⟨labels 35, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  let reserved := (runtimeTrialCost bound + 2) * attempts + 7 + fuel
  have continued := runtimeSamplerBlock_run host bound attempts (4 + fuel)
    (labels ∘ totalSamplerRetryLabels) (totalSamplerBlock_retry host attempts offset labels present)
    base range countFits
  have total : (runtimeTrialCost bound + 2) * attempts + 7 + fuel =
      (runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel) := by omega
  rw [total]
  change run host ((runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel))
    ⟨(labels ∘ totalSamplerRetryLabels) 0, base⟩ = _
  rw [continued, totalSamplerMemory, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := runtimeSamplerMemory_cost bound attempts _ memory cost supported
  have tail : totalSamplerTailCost memory ≤ 4 := by unfold totalSamplerTailCost; split <;> omega
  have remaining : totalSamplerTailCost memory ≤
      (runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel) - (cost + 1) := by omega
  have amount : (runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel) - (cost + 1) =
      ((runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel) - (cost + 1 + totalSamplerTailCost memory)) +
        totalSamplerTailCost memory := by omega
  rw [amount]
  change ((run host (_ + totalSamplerTailCost memory) ⟨labels 31, memory⟩).map _) = _
  rw [totalSamplerBlock_tail host attempts offset labels present]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  apply congrArg (fun f => PMF.map f
    (run host ((runtimeTrialCost bound + 2) * attempts + 3 + (4 + fuel) -
      (cost + 1 + totalSamplerTailCost memory)) ⟨labels 35, totalSamplerFinal memory offset⟩))
  funext outcome
  cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
