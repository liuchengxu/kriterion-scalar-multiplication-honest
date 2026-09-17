import Proof.Shared.SourceSumOrder
namespace Kriterion.ArgoMAC.Security
open scoped ENNReal
noncomputable section

/-- A comparison after each selected prefix lifts to the whole normalized source. -/
theorem weightedGhost_comparison {Key Mask Full Selected Hidden : Type*}
    (keys : PMF Key) (masks : PMF Mask) (fulls : PMF Full) (ghosts : PMF Hidden)
    (choose : Key → Mask → Full → Selected → ℝ≥0∞)
    (oldWeight : Key → Mask → Full → Selected → Hidden → ℝ≥0∞)
    (newWeight : Key → Mask → Full → Selected → ℝ≥0∞)
    (bound : ∀ selected,
      (∑' mask, masks mask * ∑' hidden, ghosts hidden * ∑' key, keys key *
        ∑' full, fulls full * (choose key mask full selected * oldWeight key mask full selected hidden)) ≤
      ∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
        (choose key mask full selected * newWeight key mask full selected)) :
    (∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
      ∑' selected, choose key mask full selected * ∑' hidden, ghosts hidden *
        oldWeight key mask full selected hidden) ≤
    ∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
      ∑' selected, choose key mask full selected * newWeight key mask full selected := by
  rw [weightedGhost_sum_order, weightedSelected_sum_order]
  apply ENNReal.tsum_le_tsum
  intro selected
  simpa only [mul_assoc] using bound selected

end
end Kriterion.ArgoMAC.Security
