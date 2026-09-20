import Proof.Privacy.Simulator.Arithmetic.PointBatchBlock
import Proof.Privacy.Simulator.Arithmetic.PointBatchLoopMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host executes the full point batch and retains the exact unused fuel. -/
theorem pointBatchBlock_run [BN254.FieldCertificate] (host : Machine) (count attempts : Nat)
    (fits : 58 * count < 2 ^ 256) (labels : Fin (58 * count + 1) → Fin (host.size + 1))
    (present : ContainsPointBatch host count attempts fits labels) (draws start fuel : Nat) (base : Memory)
    (within : start + draws ≤ count) (countFits : attempts < 2 ^ 256) :
    run host (pointBatchStepBudget attempts * draws + fuel)
      ⟨labels (pointBatchBoundary start (by omega)), base⟩ =
      (pointBatchMemory attempts start draws base).bind fun result =>
        (run host (pointBatchStepBudget attempts * draws + fuel - result.2)
          ⟨labels (pointBatchBoundary (start + draws) within), result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  induction draws generalizing fuel with
  | zero =>
      simp only [pointBatchMemory, PMF.pure_bind, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.sub_zero]
      rw [show (Option.map fun final : Configuration (host.size + 1) × Nat => (final.1, final.2)) = id from by
        funext value; cases value <;> rfl, PMF.map_id]
  | succ draws ih =>
      have inside : start + draws < count := by omega
      let selected : Fin count := ⟨start + draws, inside⟩
      conv_lhs => rw [show pointBatchStepBudget attempts * (draws + 1) + fuel =
        pointBatchStepBudget attempts * draws + (pointBatchStepBudget attempts + fuel) by rw [Nat.mul_succ]; omega]
      rw [ih (pointBatchStepBudget attempts + fuel) (by omega)]
      conv_rhs => rw [pointBatchMemory, PMF.bind_bind]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases result with ⟨memory, cost⟩
      have bounded := pointBatchMemory_cost attempts start draws base memory cost supported
      have amount : pointBatchStepBudget attempts * draws + (pointBatchStepBudget attempts + fuel) - cost =
          pointBatchStepBudget attempts + (pointBatchStepBudget attempts * draws + fuel - cost) := by omega
      rw [amount, pointBatchBlock_step host count attempts fits labels present selected _ memory countFits,
        PMF.map_bind, PMF.bind_map]
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases result with ⟨tail, spent⟩
      have tailBound := pointBatchStepMemory_cost attempts (start + draws) memory tail spent supported
      dsimp only
      have finalFuel : pointBatchStepBudget attempts + (pointBatchStepBudget attempts * draws + fuel - cost) - spent =
          pointBatchStepBudget attempts * (draws + 1) + fuel - (cost + spent) := by rw [Nat.mul_succ]; omega
      rw [finalFuel]
      simp only [PMF.map_comp, Function.comp_def, Option.map_map]
      have sameBoundary : pointBatchBoundary (start + draws + 1) inside =
          pointBatchBoundary (start + (draws + 1)) within := Fin.ext (by simp [pointBatchBoundary, Nat.add_assoc])
      rw [sameBoundary]
      apply congrArg (fun transform => PMF.map transform
        (run host (pointBatchStepBudget attempts * (draws + 1) + fuel - (cost + spent))
          ⟨labels (pointBatchBoundary (start + (draws + 1)) within), tail⟩))
      funext outcome
      cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
