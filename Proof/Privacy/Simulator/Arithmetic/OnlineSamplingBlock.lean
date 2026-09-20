import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host executes the complete online sampler and retains its exact unused fuel. -/
theorem onlineSamplingBlock_run [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 8772 → Fin (host.size + 1)) (present : ContainsOnlineSampling host attempts labels)
    (fuel : Nat) (base : Memory) (countFits : attempts < 2 ^ 256) :
    run host (onlineSamplingBudget attempts + fuel) ⟨labels 0, base⟩ =
      (onlineSamplingMemory attempts base).bind fun result =>
        (run host (onlineSamplingBudget attempts + fuel - result.2) ⟨labels 8771, result.1⟩).map
          (Option.map fun final => (final.1, final.2 + result.2)) := by
  let scaleBudget := batchStepBudget attempts * 91
  let pointBudget := pointBatchStepBudget attempts * 90
  have continued := samplerBatchBlock_run host onlineScalePlan attempts (by decide) (labels ∘ onlineScaleLabels)
    (onlineSamplingBlock_scales host attempts labels present) 91 0 (pointBudget + 2 + fuel) base (by decide) countFits
  have amount : onlineSamplingBudget attempts + fuel = scaleBudget + (pointBudget + 2 + fuel) := by
    unfold onlineSamplingBudget scaleBudget pointBudget
    omega
  conv_lhs => rw [amount]
  change run host (scaleBudget + (pointBudget + 2 + fuel))
    ⟨(labels ∘ onlineScaleLabels) (batchBoundary (count := 91) 0 (by decide)), base⟩ = _
  rw [continued, onlineSamplingMemory, PMF.bind_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  have bounded := samplerBatchMemory_cost onlineScalePlan attempts 91 0 base memory cost supported
  change cost ≤ scaleBudget at bounded
  have pointerFuel : scaleBudget + (pointBudget + 2 + fuel) - cost =
      (pointBudget + (scaleBudget + fuel - cost)) + 2 := by omega
  change (run host (scaleBudget + (pointBudget + 2 + fuel) - cost) ⟨labels 3549, memory⟩).map _ = _
  rw [pointerFuel, onlineSamplingBlock_pointer host attempts labels present]
  have points := pointBatchBlock_run host 90 attempts (by decide) (labels ∘ onlinePointLabels)
    (onlineSamplingBlock_points host attempts labels present) 90 0 (scaleBudget + fuel - cost)
    (onlinePointInitial memory) (by decide) countFits
  change run host (pointBudget + (scaleBudget + fuel - cost)) ⟨labels 3551, onlinePointInitial memory⟩ = _ at points
  rw [points, PMF.map_bind, PMF.map_bind, PMF.bind_map]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨tail, spent⟩
  have tailBound := pointBatchMemory_cost attempts 0 90 (onlinePointInitial memory) tail spent supported
  change spent ≤ pointBudget at tailBound
  dsimp only
  have finalFuel : pointBudget + (scaleBudget + fuel - cost) - spent =
      onlineSamplingBudget attempts + fuel - (cost + 2 + spent) := by
    unfold onlineSamplingBudget
    change pointBudget + (scaleBudget + fuel - cost) - spent = scaleBudget + pointBudget + 2 + fuel - (cost + 2 + spent)
    omega
  rw [finalFuel]
  simp only [PMF.map_comp, Function.comp_def, Option.map_map]
  change PMF.map _ (run host (onlineSamplingBudget attempts + fuel - (cost + 2 + spent)) ⟨labels 8771, tail⟩) = _
  apply congrArg (fun transform => PMF.map transform
    (run host (onlineSamplingBudget attempts + fuel - (cost + 2 + spent)) ⟨labels 8771, tail⟩))
  funext outcome
  cases outcome <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
