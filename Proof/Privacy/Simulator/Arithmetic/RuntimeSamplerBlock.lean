import Construction.Simulator.RuntimeSampler
import Proof.Privacy.Simulator.Arithmetic.RuntimeSamplerMemory
import Proof.Privacy.Simulator.Arithmetic.RuntimeTrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every sampler instruction before its return label. -/
def ContainsRuntimeSampler (host : Machine) (attempts : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 32, pc.val < 31 → host.code[(labels pc).val] =
    relocate labels ((runtimeSampler attempts).code[pc.val]'(by exact pc.isLt))

/-- The embedded sampler retains all runtime-trial instructions. -/
theorem runtimeSamplerBlock_trialCode (host : Machine) (attempts : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels) :
    ContainsRuntimeTrial host (labels ∘ runtimeRetryLabels) := by
  intro pc inside
  have selected := present (runtimeRetryLabels pc) (by change pc.val + 1 < 31; omega)
  have positive : 0 < pc.val + 1 := by omega
  have upper : pc.val + 1 < 27 := by omega
  have trial : (runtimeSampler attempts).code[(runtimeRetryLabels pc).val] =
      relocate runtimeRetryLabels (runtimeTrial.code[pc.val]'(by exact pc.isLt)) := by
    simp [runtimeSampler, runtimeRetryLabels, upper]
    split
    · rfl
    · rename_i impossible
      exact (impossible (by change 0 < pc.val + 1; exact positive)).elim
  exact (selected.trans (congrArg (relocate labels) trial)).trans
    (relocate_comp runtimeRetryLabels labels _)

/-- The exhausted loop clears its flag and returns after two instructions. -/
theorem runtimeSamplerBlock_zero [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (empty : base.registers 4 = 0) :
    run host (fuel + 2) ⟨labels 29, base⟩ =
      (run host fuel ⟨labels 31, {base with registers := Function.update base.registers 7 0}⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  simp [run, step, present 29 (by decide), present 30 (by decide), runtimeSampler, relocate,
    empty, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The successful trial returns after one branch instruction. -/
theorem runtimeSamplerBlock_accept [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (accepted : base.registers 7 ≠ 0) :
    run host (fuel + 1) ⟨labels 27, base⟩ =
      (run host fuel ⟨labels 31, base⟩).map (Option.map fun result => (result.1, result.2 + 1)) := by
  change base.registers 7 ≠ 0#256 at accepted
  simp [run, step, present 27 (by decide), runtimeSampler, relocate, accepted]

/-- The rejected trial decrements its counter before the next guard. -/
theorem runtimeSamplerBlock_reject [BN254.FieldCertificate] (host : Machine) (attempts fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (rejected : base.registers 7 = 0) (one : base.registers 1 = 1) :
    run host (fuel + 2) ⟨labels 27, base⟩ =
      (run host fuel
        ⟨labels 29, {base with registers := Function.update base.registers 4 (base.registers 4 - 1)}⟩).map
          (Option.map fun result => (result.1, result.2 + 2)) := by
  simp [run, step, present 27 (by decide), present 28 (by decide), runtimeSampler, relocate,
    rejected, one, Arithmetic.eval, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The guard and the trial pass memory and cost to the caller's result branch. -/
theorem runtimeSamplerBlock_trial [BN254.FieldCertificate] (host : Machine) (bound : Word) (attempts fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (range : base.registers 5 = bound) (nonzero : base.registers 4 ≠ 0#256) :
    run host (runtimeTrialCost bound + fuel) ⟨labels 29, base⟩ =
      (trialMemory (runtimeRange bound) base).bind fun memory =>
        (run host fuel ⟨labels 27, memory⟩).map
          (Option.map fun result => (result.1, result.2 + runtimeTrialCost bound)) := by
  have costPositive : 1 ≤ runtimeTrialCost bound := by exact runtimeTrialCost_positive bound
  have guard : step host ⟨labels 29, base⟩ =
      PMF.pure (some (false, ⟨(labels ∘ runtimeRetryLabels) 0, base⟩)) := by
    simp [step, present 29 (by decide), runtimeSampler, relocate, nonzero, runtimeRetryLabels, Function.comp_def]
  have continued := run_after_prefix host (runtimeTrialCost bound - 1) fuel ⟨(labels ∘ runtimeRetryLabels) 0, base⟩
  have block := runtimeTrialBlock_run host (labels ∘ runtimeRetryLabels)
    (runtimeSamplerBlock_trialCode host attempts labels present) base
  rw [range] at block
  rw [block] at continued
  rw [show runtimeTrialCost bound + fuel = (runtimeTrialCost bound - 1 + fuel) + 1 by omega,
    run, guard, PMF.pure_bind]
  change (run host (runtimeTrialCost bound - 1 + fuel) ⟨(labels ∘ runtimeRetryLabels) 0, base⟩).map
    (Option.map fun result => (result.1, result.2 + 1)) = _
  rw [continued]
  simp only [PMF.bind_map, PMF.map_bind, Function.comp_def, PMF.map_comp]
  apply congrArg (PMF.bind (trialMemory (runtimeRange bound) base))
  funext memory
  change (run host fuel ⟨labels 27, memory⟩).map _ = _
  apply congrArg (fun f => PMF.map f (run host fuel ⟨labels 27, memory⟩))
  funext result
  cases result <;> simp [Nat.add_assoc, Nat.sub_add_cancel costPositive]

/-- The complete loop returns caller memory and retains the unused fuel. -/
theorem runtimeSamplerBlock_loop [BN254.FieldCertificate] (host : Machine) (bound : Word) (attempts count fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (range : base.registers 5 = bound) (countFits : count < 2 ^ 256)
    (counter : base.registers 4 = BitVec.ofNat 256 count) :
    run host ((runtimeTrialCost bound + 2) * count + 2 + fuel) ⟨labels 29, base⟩ =
      (runtimeSamplerMemory bound count base).bind fun result =>
        (run host ((runtimeTrialCost bound + 2) * count + 2 + fuel - result.2) ⟨labels 31, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  induction count generalizing base with
  | zero =>
      have empty : base.registers 4 = 0 := by simpa using counter
      rw [runtimeSamplerMemory, PMF.pure_bind]
      simpa only [Nat.mul_zero, Nat.zero_add, Nat.add_comm, Nat.add_sub_cancel] using
        runtimeSamplerBlock_zero host attempts fuel labels present base empty
  | succ count ih =>
      have nonzero : base.registers 4 ≠ 0#256 := by
        rw [counter]
        intro equal
        have natural := congrArg BitVec.toNat equal
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countFits] at natural
        change count + 1 = 0 at natural
        omega
      have total : (runtimeTrialCost bound + 2) * (count + 1) + 2 + fuel =
          runtimeTrialCost bound + ((runtimeTrialCost bound + 2) * count + 2 + fuel + 2) := by ring
      rw [total, runtimeSamplerBlock_trial host bound attempts _ labels present base range nonzero,
        runtimeSamplerMemory, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro memory supported
      obtain ⟨same, one⟩ := trialMemory_registers (runtimeRange bound) base memory supported
      have retained := trialMemory_range bound base memory range supported
      by_cases rejected : memory.registers 7 = 0
      · rw [if_pos rejected, PMF.bind_map,
          runtimeSamplerBlock_reject host attempts _ labels present memory rejected one]
        let next : Memory := {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}
        have nextCounter : next.registers 4 = BitVec.ofNat 256 count := by
          simp only [next, Function.update_self]
          rw [same, counter, BitVec.ofNat_add]
          simp
        have previous := ih next (by simpa [next] using retained) (by omega) nextCounter
        change ((run host ((runtimeTrialCost bound + 2) * count + 2 + fuel) ⟨labels 29, next⟩).map _).map _ = _
        rw [previous]
        simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
        apply congrArg (PMF.bind (runtimeSamplerMemory bound count next))
        funext result
        rcases result with ⟨final, cost⟩
        have remaining : runtimeTrialCost bound + ((runtimeTrialCost bound + 2) * count + 2 + fuel + 2) -
            (cost + runtimeTrialCost bound + 2) = (runtimeTrialCost bound + 2) * count + 2 + fuel - cost := by omega
        rw [remaining]
        apply congrArg (fun f => PMF.map f
          (run host ((runtimeTrialCost bound + 2) * count + 2 + fuel - cost) ⟨labels 31, final⟩))
        funext result
        cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · rw [if_neg rejected, PMF.pure_bind]
        rw [show (runtimeTrialCost bound + 2) * count + 2 + fuel + 2 =
          ((runtimeTrialCost bound + 2) * count + 2 + fuel + 1) + 1 by omega,
          runtimeSamplerBlock_accept host attempts _ labels present memory rejected]
        have remaining : runtimeTrialCost bound + (((runtimeTrialCost bound + 2) * count + 2 + fuel + 1) + 1) -
            (runtimeTrialCost bound + 1) = (runtimeTrialCost bound + 2) * count + 2 + fuel + 1 := by omega
        rw [remaining]
        simp only [PMF.map_comp, Function.comp_def, Option.map_map]
        apply congrArg (fun f => PMF.map f (run host ((runtimeTrialCost bound + 2) * count + 2 + fuel + 1)
          ⟨labels 31, memory⟩))
        funext result
        cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The caller resumes after the complete sampler and retains every unused fuel unit. -/
theorem runtimeSamplerBlock_run [BN254.FieldCertificate] (host : Machine) (bound : Word) (attempts fuel : Nat)
    (labels : Fin 32 → Fin (host.size + 1)) (present : ContainsRuntimeSampler host attempts labels)
    (base : Memory) (range : base.registers 5 = bound) (countFits : attempts < 2 ^ 256) :
    run host ((runtimeTrialCost bound + 2) * attempts + 3 + fuel) ⟨labels 0, base⟩ =
      (runtimeSamplerMemory bound attempts
        {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}).bind fun result =>
          (run host ((runtimeTrialCost bound + 2) * attempts + 3 + fuel - (result.2 + 1))
            ⟨labels 31, result.1⟩).map (Option.map fun final => (final.1, final.2 + result.2 + 1)) := by
  let initialized : Memory := {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)}
  have entry : step host ⟨labels 0, base⟩ = PMF.pure (some (false, ⟨labels 29, initialized⟩)) := by
    simp [step, present 0 (by decide), runtimeSampler, relocate, initialized]
  have loop := runtimeSamplerBlock_loop host bound attempts attempts fuel labels present initialized
    (by simpa [initialized] using range) countFits (by simp [initialized])
  rw [show (runtimeTrialCost bound + 2) * attempts + 3 + fuel =
    ((runtimeTrialCost bound + 2) * attempts + 2 + fuel) + 1 by omega, run, entry, PMF.pure_bind]
  change (run host ((runtimeTrialCost bound + 2) * attempts + 2 + fuel) ⟨labels 29, initialized⟩).map _ = _
  rw [loop, PMF.map_bind]
  apply congrArg (PMF.bind (runtimeSamplerMemory bound attempts initialized))
  funext result
  rcases result with ⟨memory, cost⟩
  have remaining : ((runtimeTrialCost bound + 2) * attempts + 2 + fuel) + 1 - (cost + 1) =
      (runtimeTrialCost bound + 2) * attempts + 2 + fuel - cost := by omega
  rw [remaining]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
