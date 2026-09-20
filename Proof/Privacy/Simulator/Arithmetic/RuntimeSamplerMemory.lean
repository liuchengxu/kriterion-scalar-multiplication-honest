import Proof.Privacy.Simulator.Arithmetic.RuntimeTrial
import Proof.Privacy.Simulator.Arithmetic.SamplerMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This law retains the retry memory and the runtime trial cost before the final halt. -/
noncomputable def runtimeSamplerMemory (bound : Word) : Nat → Memory → PMF (Memory × Nat)
  | 0, base => PMF.pure ({base with registers := Function.update base.registers 7 0}, 2)
  | count + 1, base => (trialMemory (runtimeRange bound) base).bind fun memory =>
      if memory.registers 7 = 0 then
        (runtimeSamplerMemory bound count
          {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}).map
            fun result => (result.1, result.2 + runtimeTrialCost bound + 2)
      else PMF.pure (memory, runtimeTrialCost bound + 1)

/-- Runtime width calculation changes the cost but preserves the source memory law. -/
theorem runtimeSamplerMemory_memory (bound : Word) (count : Nat) (base : Memory) :
    (runtimeSamplerMemory bound count base).map Prod.fst =
      (samplerMemory (runtimeRange bound) count base).map Prod.fst := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp only [runtimeSamplerMemory, samplerMemory, PMF.map_bind]
      apply congrArg (PMF.bind (trialMemory (runtimeRange bound) base))
      funext memory
      split
      · simpa only [PMF.map_comp, Function.comp_def] using
          ih {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}
      · simp only [PMF.pure_map]

/-- Every runtime retry reserves its trial and two control instructions. -/
theorem runtimeSamplerMemory_cost (bound : Word) (count : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (runtimeSamplerMemory bound count base).support) :
    cost ≤ (runtimeTrialCost bound + 2) * count + 2 := by
  induction count generalizing base final cost with
  | zero =>
      simp only [runtimeSamplerMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      obtain ⟨_, rfl⟩ := supported
      omega
  | succ count ih =>
      obtain ⟨memory, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      split at supported
      · obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rcases result with ⟨next, steps⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        have tail := ih _ _ _ member
        simp only [Nat.mul_succ]
        omega
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        obtain ⟨_, rfl⟩ := supported
        simp only [Nat.mul_succ]
        omega

/-- The runtime trial preserves its encoded range. -/
theorem trialMemory_range (bound : Word) (base memory : Memory)
    (range : base.registers 5 = bound)
    (supported : memory ∈ (trialMemory (runtimeRange bound) base).support) :
    memory.registers 5 = bound := by
  unfold trialMemory at supported
  split at supported
  · obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨bit, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    simpa [fullTrialFrame, wideFrame, frame] using range
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    simpa [narrowTrialFrame] using runtimeRange_word bound

/-- The runtime memory law gives the exact source cutoff law. -/
theorem runtimeSamplerMemory_source [BN254.FieldCertificate] (bound : Word) (count : Nat) (base : Memory) :
    (runtimeSamplerMemory bound count base).map (fun result => trialValue result.1) =
      (Security.BoundedIntegerSampling.cutoff (runtimeRange bound) count).law.map
        (Option.map fun value => BitVec.ofNat 256 value.val) := by
  have memory := congrArg (PMF.map trialValue) (runtimeSamplerMemory_memory bound count base)
  simp only [PMF.map_comp, Function.comp_def] at memory
  rw [memory]
  have source := congrArg (PMF.map Prod.fst)
    (samplerMemory_source (runtimeRange bound) count base
      (runtimeRange_bounds _).1 (runtimeRange_bounds _).2)
  simp only [PMF.map_comp, Function.comp_def] at source
  rw [source]
  exact retryLaw_source (runtimeRange bound) count

/-- Every runtime result also occurs in the fixed-range memory law. -/
theorem runtimeSamplerMemory_support (bound : Word) (count : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (runtimeSamplerMemory bound count base).support) :
    ∃ sourceCost, (final, sourceCost) ∈ (samplerMemory (runtimeRange bound) count base).support := by
  have projected : final ∈ ((runtimeSamplerMemory bound count base).map Prod.fst).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, rfl⟩
  rw [runtimeSamplerMemory_memory] at projected
  obtain ⟨⟨memory, sourceCost⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
  change memory = final at equal
  subst memory
  exact ⟨sourceCost, member⟩

/-- The runtime sampler preserves the caller's stacks and RAM. -/
theorem runtimeSamplerMemory_data (bound : Word) (count : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (runtimeSamplerMemory bound count base).support) :
    final.bits = base.bits ∧ final.ram = base.ram := by
  obtain ⟨sourceCost, member⟩ := runtimeSamplerMemory_support bound count base final cost supported
  exact samplerMemory_data (runtimeRange bound) count base final sourceCost member

/-- The runtime sampler preserves registers eight through fifteen. -/
theorem runtimeSamplerMemory_caller (bound : Word) (count : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 8 ≤ register.val)
    (supported : (final, cost) ∈ (runtimeSamplerMemory bound count base).support) :
    final.registers register = base.registers register := by
  obtain ⟨sourceCost, member⟩ := runtimeSamplerMemory_support bound count base final cost supported
  exact samplerMemory_caller (runtimeRange bound) count base final sourceCost register caller member

/-- The runtime sampler preserves its encoded range. -/
theorem runtimeSamplerMemory_range (bound : Word) (count : Nat) (base final : Memory) (cost : Nat)
    (range : base.registers 5 = bound)
    (supported : (final, cost) ∈ (runtimeSamplerMemory bound count base).support) :
    final.registers 5 = bound := by
  induction count generalizing base final cost with
  | zero =>
      simp only [runtimeSamplerMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      obtain ⟨rfl, _⟩ := supported
      simpa using range
  | succ count ih =>
      obtain ⟨memory, trial, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have retained := trialMemory_range bound base memory range trial
      split at supported
      · obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rcases result with ⟨next, steps⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        exact ih _ _ _ (by simpa using retained) member
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        obtain ⟨rfl, rfl⟩ := supported
        exact retained

end Kriterion.ArgoMAC.ArithmeticSimulator
