import Proof.Privacy.Simulator.Arithmetic.PointBatchMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The point batch appends each draw in the source vector order. -/
noncomputable def pointBatchMemory [BN254.FieldCertificate] (attempts start : Nat) :
    Nat → Memory → PMF (Memory × Nat)
  | 0, base => PMF.pure (base, 0)
  | count + 1, base => (pointBatchMemory attempts start count base).bind fun first =>
      (pointBatchStepMemory attempts (start + count) first.1).map fun second =>
        (second.1, first.2 + second.2)

/-- Every point batch fits its fixed instruction budget. -/
theorem pointBatchMemory_cost [BN254.FieldCertificate] (attempts start count : Nat)
    (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointBatchMemory attempts start count base).support) :
    cost ≤ pointBatchStepBudget attempts * count := by
  induction count generalizing final cost with
  | zero =>
      simp only [pointBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      omega
  | succ count ih =>
      obtain ⟨⟨memory, spent⟩, first, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨⟨tail, tailCost⟩, second, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      have firstCost := ih memory spent first
      have secondCost := pointBatchStepMemory_cost attempts (start + count) memory tail tailCost second
      dsimp only
      rw [Nat.mul_succ]
      omega

/-- The point batch preserves all caller stacks. -/
theorem pointBatchMemory_bits [BN254.FieldCertificate] (attempts start count : Nat)
    (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointBatchMemory attempts start count base).support) :
    final.bits = base.bits := by
  induction count generalizing final cost with
  | zero =>
      simp only [pointBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      exact congrArg Memory.bits supported.1
  | succ count ih =>
      obtain ⟨⟨memory, spent⟩, first, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨⟨tail, tailCost⟩, second, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact (pointBatchStepMemory_bits attempts (start + count) memory tail tailCost second).trans
        (ih memory spent first)

/-- The point batch preserves registers nine through fifteen. -/
theorem pointBatchMemory_caller [BN254.FieldCertificate] (attempts start count : Nat)
    (base final : Memory) (cost : Nat) (register : Register) (caller : 9 ≤ register.val)
    (supported : (final, cost) ∈ (pointBatchMemory attempts start count base).support) :
    final.registers register = base.registers register := by
  induction count generalizing final cost with
  | zero =>
      simp only [pointBatchMemory, PMF.mem_support_pure_iff, Prod.mk.injEq] at supported
      exact congrArg (fun memory => memory.registers register) supported.1
  | succ count ih =>
      obtain ⟨⟨memory, spent⟩, first, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      obtain ⟨⟨tail, tailCost⟩, second, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
      exact (pointBatchStepMemory_caller attempts (start + count) memory tail tailCost register caller second).trans
        (ih memory spent first)

end Kriterion.ArgoMAC.ArithmeticSimulator
