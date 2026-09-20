import Proof.Privacy.Simulator.Arithmetic.SamplerBatchCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The store tail writes the sampled word at its scheduled address. -/
def batchStored (base : Memory) (index : Nat) : Memory :=
  {base with
    registers := Function.update base.registers 8 (base.registers 10 + BitVec.ofNat 256 index)
    ram := Function.update base.ram (base.registers 10 + BitVec.ofNat 256 index) (base.registers 0)}

/-- Each batch step loads its range, samples its word, and stores its word. -/
noncomputable def batchStepMemory (spec : DrawSpec) (attempts index : Nat) (base : Memory) : PMF (Memory × Nat) :=
  (totalSamplerMemory spec.1 attempts spec.2
    {base with registers := Function.update base.registers 5 spec.1}).map fun result =>
      (batchStored result.1 index, result.2 + 4)

/-- This budget covers every scheduled range and all four load/store instructions. -/
def batchStepBudget (attempts : Nat) : Nat := 2574 * attempts + 11

/-- Every batch step fits in its uniform instruction budget. -/
theorem batchStepMemory_cost (spec : DrawSpec) (attempts index : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (batchStepMemory spec attempts index base).support) :
    cost ≤ batchStepBudget attempts := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have bounded := totalSamplerMemory_cost spec.1 attempts spec.2 _ memory spent member
  have product := Nat.mul_le_mul_right attempts
    (show runtimeTrialCost spec.1 + 2 ≤ 2574 by have h := runtimeTrialCost_bound spec.1; omega)
  dsimp only
  unfold batchStepBudget
  omega

/-- Each batch step preserves registers nine through fifteen. -/
theorem batchStepMemory_caller (spec : DrawSpec) (attempts index : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 9 ≤ register.val)
    (supported : (final, cost) ∈ (batchStepMemory spec attempts index base).support) :
    final.registers register = base.registers register := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have different (target : Register) (localRegister : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  have retained := totalSamplerMemory_caller spec.1 attempts spec.2 _ memory spent register (by omega) member
  dsimp only [batchStored]
  rw [Function.update_of_ne (different 8 (by decide))]
  simpa only [Function.update_of_ne (different 5 (by decide))] using retained

/-- Each batch step preserves the caller's stacks. -/
theorem batchStepMemory_bits (spec : DrawSpec) (attempts index : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (batchStepMemory spec attempts index base).support) :
    final.bits = base.bits := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (totalSamplerMemory_data spec.1 attempts spec.2
    {base with registers := Function.update base.registers 5 spec.1} memory spent member).1

/-- The only RAM change writes the returned word at the caller's base address plus its index. -/
theorem batchStepMemory_ram (spec : DrawSpec) (attempts index : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (batchStepMemory spec attempts index base).support) :
    final.ram = Function.update base.ram (base.registers 10 + BitVec.ofNat 256 index) (final.registers 0) := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have retained := (totalSamplerMemory_data spec.1 attempts spec.2
    {base with registers := Function.update base.registers 5 spec.1} memory spent member).2
  have pointer := totalSamplerMemory_caller spec.1 attempts spec.2
    {base with registers := Function.update base.registers 5 spec.1} memory spent 10 (by decide) member
  dsimp only at retained pointer
  simp only [Function.update_of_ne (by decide : (10 : Register) ≠ 5)] at pointer
  dsimp only [batchStored]
  rw [retained, pointer, Function.update_of_ne (by decide : (0 : Register) ≠ 8)]

/-- The scheduled word has the exact total-integer source law. -/
theorem batchStepMemory_source [BN254.FieldCertificate] (spec : DrawSpec) (attempts index : Nat) (base : Memory) :
    (batchStepMemory spec attempts index base).map (fun result => result.1.registers 0) =
      (Security.BoundedIntegerSampling.totalInteger (runtimeRange spec.1) (runtimeRange_bounds spec.1).1 attempts).law.map
        (fun value => BitVec.ofNat 256 value.val + spec.2) := by
  rw [batchStepMemory, PMF.map_comp]
  simp only [Function.comp_def, batchStored, Function.update_of_ne (by decide : (0 : Register) ≠ 8)]
  exact totalSamplerMemory_source spec.1 attempts spec.2 _

/-- The batch return law executes the scheduled memory updates in order. -/
noncomputable def samplerBatchMemory {count : Nat} (plan : Vector DrawSpec count) (attempts : Nat) :
    Nat → Nat → Memory → PMF (Memory × Nat)
  | 0, _, base => PMF.pure (base, 0)
  | remaining + 1, index, base =>
      if inside : index < count then
        (batchStepMemory plan[index] attempts index base).bind fun result =>
          (samplerBatchMemory plan attempts remaining (index + 1) result.1).map fun final =>
            (final.1, final.2 + result.2)
      else PMF.pure (base, 0)

/-- Every batch return cost fits in the sum of its fixed step budgets. -/
theorem samplerBatchMemory_cost {count : Nat} (plan : Vector DrawSpec count) (attempts remaining index : Nat)
    (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerBatchMemory plan attempts remaining index base).support) :
    cost ≤ batchStepBudget attempts * remaining := by
  induction remaining generalizing index base final cost with
  | zero =>
      simp only [samplerBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      obtain ⟨_, rfl⟩ := supported
      omega
  | succ remaining ih =>
      simp only [samplerBatchMemory] at supported
      split at supported
      · obtain ⟨⟨memory, spent⟩, stepSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        obtain ⟨⟨tail, tailCost⟩, tailSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        have first := batchStepMemory_cost _ attempts index base memory spent stepSupport
        have rest := ih (index + 1) memory tail tailCost tailSupport
        dsimp only
        simp only [Nat.mul_succ]
        omega
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        obtain ⟨_, rfl⟩ := supported
        omega

/-- The complete batch preserves registers nine through fifteen. -/
theorem samplerBatchMemory_caller {count : Nat} (plan : Vector DrawSpec count) (attempts remaining index : Nat)
    (base final : Memory) (cost : Nat) (register : Register) (caller : 9 ≤ register.val)
    (supported : (final, cost) ∈ (samplerBatchMemory plan attempts remaining index base).support) :
    final.registers register = base.registers register := by
  induction remaining generalizing index base final cost with
  | zero =>
      simp only [samplerBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      exact congrArg (fun memory => memory.registers register) supported.1
  | succ remaining ih =>
      simp only [samplerBatchMemory] at supported
      split at supported
      · obtain ⟨⟨memory, spent⟩, stepSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        obtain ⟨⟨tail, tailCost⟩, tailSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        exact (ih (index + 1) memory tail tailCost tailSupport).trans
          (batchStepMemory_caller _ attempts index base memory spent register caller stepSupport)
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        exact congrArg (fun memory => memory.registers register) supported.1

/-- The complete batch preserves all caller stacks. -/
theorem samplerBatchMemory_bits {count : Nat} (plan : Vector DrawSpec count) (attempts remaining index : Nat)
    (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerBatchMemory plan attempts remaining index base).support) :
    final.bits = base.bits := by
  induction remaining generalizing index base final cost with
  | zero =>
      simp only [samplerBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      exact congrArg Memory.bits supported.1
  | succ remaining ih =>
      simp only [samplerBatchMemory] at supported
      split at supported
      · obtain ⟨⟨memory, spent⟩, stepSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        obtain ⟨⟨tail, tailCost⟩, tailSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        exact (ih (index + 1) memory tail tailCost tailSupport).trans
          (batchStepMemory_bits _ attempts index base memory spent stepSupport)
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        exact congrArg Memory.bits supported.1

end Kriterion.ArgoMAC.ArithmeticSimulator
