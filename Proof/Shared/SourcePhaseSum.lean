import Proof.Shared.SourceHCoefficient

namespace Kriterion.ArgoMAC.Security
open scoped ENNReal
noncomputable section

/-- The sample indicator sum gives the exact guarded event mass. -/
theorem phase_sum_event {Sample : Type*} (samples : PMF Sample)
    (factor : ℝ≥0∞) (guard : Prop) [Decidable guard] (event : Set Sample)
    [DecidablePred (fun sample => sample ∈ event)] (weight : Sample → ℝ≥0∞)
    (pointwise : ∀ sample, weight sample = factor * (if guard ∧ sample ∈ event then 1 else 0)) :
    (∑' sample, samples sample * weight sample) =
      factor * (if guard then samples.toOuterMeasure event else 0) := by
  classical
  simp_rw [pointwise]
  by_cases kept : guard
  · simp only [kept, true_and, if_true, PMF.toOuterMeasure_apply,
      Set.indicator_apply, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro sample
    by_cases member : sample ∈ event <;> simp [member, mul_comm]
  · simp [kept]

/-- Both outer source sums retain one common phase factor and the exact event mass. -/
theorem source_phase_sum_event {Rest Tag Sample : Type*}
    (rests : PMF Rest) (tags : PMF Tag) (samples : PMF Sample)
    (factor : ℝ≥0∞) (guard : Rest → Prop) [DecidablePred guard]
    (event : Rest → Tag → Set Sample)
    [∀ rest tag, DecidablePred (fun sample => sample ∈ event rest tag)]
    (weight : Rest → Tag → Sample → ℝ≥0∞)
    (pointwise : ∀ rest tag sample,
      weight rest tag sample = factor * (if guard rest ∧ sample ∈ event rest tag then 1 else 0)) :
    (∑' rest, rests rest * ∑' tag, tags tag * ∑' sample, samples sample * weight rest tag sample) =
      factor * ∑' rest, rests rest * ∑' tag, tags tag *
        (if guard rest then samples.toOuterMeasure (event rest tag) else 0) := by
  simp_rw [phase_sum_event samples factor (guard _) (event _ _) (weight _ _) (pointwise _ _)]
  simp only [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro rest
  apply tsum_congr
  intro tag
  ac_rfl

end
end Kriterion.ArgoMAC.Security
