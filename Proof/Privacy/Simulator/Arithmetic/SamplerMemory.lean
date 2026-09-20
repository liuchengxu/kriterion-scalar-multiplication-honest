import Proof.Privacy.Simulator.Arithmetic.BoundedSampler

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This law retains the memory and the cost before the sampler returns to its caller. -/
noncomputable def samplerMemory (size : Nat) : Nat → Memory → PMF (Memory × Nat)
  | 0, base => PMF.pure ({base with registers := Function.update base.registers 7 0}, 2)
  | count + 1, base => (trialMemory size base).bind fun memory =>
      if memory.registers 7 = 0 then
        (samplerMemory size count
          {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}).map
            fun result => (result.1, result.2 + trialCost size + 2)
      else PMF.pure (memory, trialCost size + 1)

/-- The memory law gives the same accepted word and cost as the source retry law. -/
theorem samplerMemory_source [BN254.FieldCertificate] (size count : Nat) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (samplerMemory size count base).map (fun result => (trialValue result.1, result.2 + 1)) =
      retryLaw size count := by
  induction count generalizing base with
  | zero => simp [samplerMemory, retryLaw, PMF.pure_map, trialValue]
  | succ count ih =>
      rw [samplerMemory, PMF.map_bind, retryLaw_memory size count base positive bounded]
      apply congrArg (PMF.bind (trialMemory size base))
      funext memory
      by_cases rejected : memory.registers 7 = 0
      · simp only [rejected, ite_true, trialValue]
        have previous := ih {memory with registers := Function.update memory.registers 4 (memory.registers 4 - 1)}
        have projected := congrArg
          (PMF.map (fun result : Option Word × Nat => (result.1, result.2 + trialCost size + 2))) previous
        simpa only [trialValue, PMF.map_comp, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using projected
      · simp only [if_neg rejected, trialValue]
        simp only [PMF.pure_map, if_neg rejected, Nat.add_assoc]

/-- Every supported trial preserves stacks and RAM. -/
theorem trialMemory_data (size : Nat) (base memory : Memory)
    (supported : memory ∈ (trialMemory size base).support) :
    memory.bits = base.bits ∧ memory.ram = base.ram := by
  unfold trialMemory at supported
  split at supported
  · obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨bit, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    exact ⟨rfl, rfl⟩
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    exact ⟨rfl, rfl⟩

/-- The complete sampler preserves the caller's stacks and RAM. -/
theorem samplerMemory_data (size count : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerMemory size count base).support) :
    final.bits = base.bits ∧ final.ram = base.ram := by
  induction count generalizing base final cost with
  | zero =>
      simp only [samplerMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      obtain ⟨rfl, _⟩ := supported
      exact ⟨rfl, rfl⟩
  | succ count ih =>
      obtain ⟨memory, trial, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have retained := trialMemory_data size base memory trial
      split at supported
      · obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rcases result with ⟨next, steps⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        have tail := ih _ _ _ member
        exact ⟨tail.1.trans retained.1, tail.2.trans retained.2⟩
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        obtain ⟨rfl, rfl⟩ := supported
        exact retained

/-- The sampler returns within its reserved prefix budget. -/
theorem samplerMemory_cost (size count : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerMemory size count base).support) :
    cost ≤ (trialCost size + 2) * count + 2 := by
  induction count generalizing base final cost with
  | zero =>
      simp only [samplerMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
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

/-- Each supported trial preserves registers eight through fifteen. -/
theorem trialMemory_caller (size : Nat) (base memory : Memory) (register : Register)
    (caller : 8 ≤ register.val) (supported : memory ∈ (trialMemory size base).support) :
    memory.registers register = base.registers register := by
  have different (target : Register) (localRegister : target.val < 8) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  unfold trialMemory at supported
  split at supported
  · obtain ⟨value, _, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨bit, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    dsimp only [fullTrialFrame, wideFrame, frame]
    rw [Function.update_of_ne (different 7 (by decide)), Function.update_of_ne (different 6 (by decide)),
      Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 1 (by decide)),
      Function.update_of_ne (different 2 (by decide)), Function.update_of_ne (different 3 (by decide))]
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    subst memory
    dsimp only [narrowTrialFrame, wideFrame, frame]
    rw [Function.update_of_ne (different 7 (by decide)), Function.update_of_ne (different 5 (by decide)),
      Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 0 (by decide)),
      Function.update_of_ne (different 1 (by decide)), Function.update_of_ne (different 2 (by decide)),
      Function.update_of_ne (different 3 (by decide))]

/-- The complete sampler preserves registers eight through fifteen. -/
theorem samplerMemory_caller (size count : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 8 ≤ register.val)
    (supported : (final, cost) ∈ (samplerMemory size count base).support) :
    final.registers register = base.registers register := by
  have different (target : Register) (localRegister : target.val < 8) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  induction count generalizing base final cost with
  | zero =>
      simp only [samplerMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      obtain ⟨rfl, _⟩ := supported
      exact Function.update_of_ne (different 7 (by decide)) _ _
  | succ count ih =>
      obtain ⟨memory, trial, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      have retained := trialMemory_caller size base memory register caller trial
      split at supported
      · obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        rcases result with ⟨next, steps⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
        have tail := ih _ _ _ member
        dsimp only at tail
        rw [Function.update_of_ne (different 4 (by decide))] at tail
        exact tail.trans retained
      · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
        obtain ⟨rfl, rfl⟩ := supported
        exact retained

end Kriterion.ArgoMAC.ArithmeticSimulator
