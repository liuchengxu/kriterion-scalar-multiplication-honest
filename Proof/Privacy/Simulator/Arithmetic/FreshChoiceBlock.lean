import Proof.Privacy.Simulator.Arithmetic.FreshChoiceState
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the fresh-choice block and supplies its return instruction. -/
def ContainsFreshChoice (host : Machine) (attempts : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 67, pc ≠ 66 → host.code[(labels pc).val] =
    relocate labels ((freshChoice attempts).code[pc.val]'(by exact pc.isLt))

/-- The embedded fresh-choice block contains the complete runtime sampler. -/
theorem freshChoiceBlock_sampler (host : Machine) (attempts : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) (present : ContainsFreshChoice host attempts labels) :
    ContainsRuntimeSampler host attempts (labels ∘ freshSamplerLabels) := by
  intro pc inside
  have valid : freshSamplerLabels pc ≠ 66 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [freshSamplerLabels] at values
    omega
  exact (present (freshSamplerLabels pc) valid).trans
    ((congrArg (relocate labels) (freshChoice_sampler attempts pc inside)).trans
      (relocate_comp freshSamplerLabels labels _))

/-- The embedded block prepares the runtime sampler in fifteen instructions. -/
theorem freshChoiceBlock_setup [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) (present : ContainsFreshChoice host attempts labels)
    (memory : Memory) :
    runPrefix host 15 ⟨labels 0, memory⟩ =
      PMF.pure (some (false, ⟨labels 15, freshChoiceInitial memory⟩, 15)) := by
  simp [runPrefix, step, present 0 (by decide), present 1 (by decide), present 2 (by decide),
    present 3 (by decide), present 4 (by decide), present 5 (by decide), present 6 (by decide),
    present 7 (by decide), present 8 (by decide), present 9 (by decide), present 10 (by decide),
    present 11 (by decide), present 12 (by decide), present 13 (by decide), present 14 (by decide),
    freshChoice, relocate, freshChoiceInitial, oracleSaved, Arithmetic.eval,
    PMF.pure_map, Function.update_comm]

/-- The embedded block restores metadata in sixteen instructions. -/
theorem freshChoiceBlock_restore [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) (present : ContainsFreshChoice host attempts labels)
    (memory : Memory) :
    runPrefix host 16 ⟨labels 46, memory⟩ =
      PMF.pure (some (false, ⟨labels 62, oracleRestored memory⟩, 16)) := by
  simp [runPrefix, step, present 46 (by decide), present 47 (by decide), present 48 (by decide),
    present 49 (by decide), present 50 (by decide), present 51 (by decide), present 52 (by decide),
    present 53 (by decide), present 54 (by decide), present 55 (by decide), present 56 (by decide),
    present 57 (by decide), present 58 (by decide), present 59 (by decide), present 60 (by decide),
    present 61 (by decide), freshChoice, relocate, oracleRestored, Arithmetic.eval,
    PMF.pure_map, Function.update_comm]

/-- The final prefix returns before the host executes its continuation. -/
theorem freshChoiceBlock_tail [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) (present : ContainsFreshChoice host attempts labels)
    (memory : Memory) :
    runPrefix host (freshChoiceTailCost memory - 1) ⟨labels 46, memory⟩ =
      PMF.pure (some (false, ⟨labels 66, freshChoiceFinal memory⟩, freshChoiceTailCost memory - 1)) := by
  have cost : freshChoiceTailCost memory - 1 =
      16 + (if memory.registers 7 = 0#256 then 1 else 4) := by
    unfold freshChoiceTailCost
    split <;> rfl
  rw [cost, prefix_add, freshChoiceBlock_restore host attempts labels present memory, PMF.pure_bind]
  dsimp only
  by_cases failed : memory.registers 7 = 0#256
  · simp [failed, runPrefix, step, present 62 (by decide), freshChoice, relocate,
      oracleRestored, freshChoiceFinal, PMF.pure_map]
  · simp [failed, runPrefix, step, present 62 (by decide), present 63 (by decide),
      present 64 (by decide), present 65 (by decide), freshChoice, relocate,
      oracleRestored, freshChoiceFinal, Arithmetic.eval, PMF.pure_map, Function.update_comm]

/-- The final prefix uses at most twenty instructions and includes no caller instruction. -/
theorem freshChoiceTailCost_bounds (memory : Memory) :
    1 ≤ freshChoiceTailCost memory ∧ freshChoiceTailCost memory - 1 ≤ 20 := by
  unfold freshChoiceTailCost
  split <;> omega

/-- The fresh-choice block retains the unused fuel and complete memory at its return. -/
theorem freshChoiceBlock_run [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 67 → Fin (host.size + 1)) (present : ContainsFreshChoice host attempts labels)
    (memory : Memory) (countFits : attempts < 2 ^ 256) :
    let reserve := (runtimeTrialCost (memory.registers 5 - memory.registers 0) + 2) * attempts + 3 + (20 + fuel)
    run host (15 + reserve) ⟨labels 0, memory⟩ =
      (freshChoiceSamples attempts memory).bind fun result =>
        (run host (reserve - (result.2 + 1) - (freshChoiceTailCost result.1 - 1))
          ⟨labels 66, freshChoiceFinal result.1⟩).map
          (Option.map fun final => (final.1,
            final.2 + (freshChoiceTailCost result.1 - 1) + (result.2 + 1) + 15)) := by
  dsimp only
  let bound := memory.registers 5 - memory.registers 0
  let initial := freshChoiceInitial memory
  let initialized : Memory :=
    {initial with registers := Function.update initial.registers 4 (BitVec.ofNat 256 attempts)}
  have continued := runtimeSamplerBlock_run host bound attempts (20 + fuel)
    (labels ∘ freshSamplerLabels) (freshChoiceBlock_sampler host attempts labels present) initial
    (by simp [initial, freshChoiceInitial, bound]) countFits
  rw [run_after_prefix, freshChoiceBlock_setup host attempts labels present memory, PMF.pure_bind]
  dsimp only
  change (run host _ ⟨(labels ∘ freshSamplerLabels) 0, initial⟩).map _ = _
  rw [continued, PMF.map_bind]
  change (runtimeSamplerMemory bound attempts initialized).bind _ =
    (runtimeSamplerMemory bound attempts initialized).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨sampled, cost⟩
  have costBound := runtimeSamplerMemory_cost bound attempts initialized sampled cost supported
  have tailBound := freshChoiceTailCost_bounds sampled
  have available : freshChoiceTailCost sampled - 1 ≤
      (runtimeTrialCost bound + 2) * attempts + 3 + (20 + fuel) - (cost + 1) := by omega
  change ((run host _ ⟨labels 46, sampled⟩).map _).map _ = _
  conv_lhs => arg 2; arg 2; arg 2; rw [show
    (runtimeTrialCost bound + 2) * attempts + 3 + (20 + fuel) - (cost + 1) =
      (freshChoiceTailCost sampled - 1) +
        ((runtimeTrialCost bound + 2) * attempts + 3 + (20 + fuel) - (cost + 1) -
          (freshChoiceTailCost sampled - 1)) by omega]
  rw [run_after_prefix, freshChoiceBlock_tail host attempts labels present sampled, PMF.pure_bind]
  dsimp only
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
