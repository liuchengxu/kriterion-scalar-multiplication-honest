import Proof.Shared.SourceGoodMass
namespace Kriterion.ArgoMAC.Security
open scoped ENNReal
noncomputable section

private def ghostSumOrder {Key Mask Full Selected Hidden : Type*} :
    Key × Mask × Full × Selected × Hidden ≃ Selected × Mask × Hidden × Key × Full where
  toFun coin := (coin.2.2.2.1, coin.2.1, coin.2.2.2.2, coin.1, coin.2.2.1)
  invFun coin := (coin.2.2.2.1, coin.2.1, coin.2.2.2.2, coin.1, coin.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

private theorem ghost_sum_order {Key Mask Full Selected Hidden : Type*}
    (weight : Key → Mask → Full → Selected → Hidden → ℝ≥0∞) :
    (∑' key, ∑' mask, ∑' full, ∑' selected, ∑' hidden, weight key mask full selected hidden) =
      ∑' selected, ∑' mask, ∑' hidden, ∑' key, ∑' full, weight key mask full selected hidden := by
  have reorder := ghostSumOrder.symm.tsum_eq
    (fun coin : Key × Mask × Full × Selected × Hidden =>
      weight coin.1 coin.2.1 coin.2.2.1 coin.2.2.2.1 coin.2.2.2.2)
  simpa only [ENNReal.tsum_prod', ghostSumOrder, Equiv.coe_fn_symm_mk] using reorder.symm

/-- The exact source sum places the selected prefix before the key and mask transport. -/
theorem weightedGhost_sum_order {Key Mask Full Selected Hidden : Type*}
    (keys : PMF Key) (masks : PMF Mask) (fulls : PMF Full) (ghosts : PMF Hidden)
    (choose : Key → Mask → Full → Selected → ℝ≥0∞)
    (weight : Key → Mask → Full → Selected → Hidden → ℝ≥0∞) :
    (∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
      ∑' selected, choose key mask full selected * ∑' hidden, ghosts hidden *
        weight key mask full selected hidden) =
    ∑' selected, ∑' mask, masks mask * ∑' hidden, ghosts hidden *
      ∑' key, keys key * ∑' full, fulls full * choose key mask full selected *
        weight key mask full selected hidden := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ghost_sum_order]
  apply tsum_congr
  intro selected
  apply tsum_congr
  intro mask
  apply tsum_congr
  intro hidden
  apply tsum_congr
  intro key
  apply tsum_congr
  intro full
  ac_rfl

private def selectedSumOrder {Key Mask Full Selected : Type*} :
    Key × Mask × Full × Selected ≃ Selected × Key × Mask × Full where
  toFun coin := (coin.2.2.2, coin.1, coin.2.1, coin.2.2.1)
  invFun coin := (coin.2.1, coin.2.2.1, coin.2.2.2, coin.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact source sum restores the retained order after the selected-prefix comparison. -/
theorem weightedSelected_sum_order {Key Mask Full Selected : Type*}
    (keys : PMF Key) (masks : PMF Mask) (fulls : PMF Full)
    (choose : Key → Mask → Full → Selected → ℝ≥0∞)
    (weight : Key → Mask → Full → Selected → ℝ≥0∞) :
    (∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
      ∑' selected, choose key mask full selected * weight key mask full selected) =
    ∑' selected, ∑' key, keys key * ∑' mask, masks mask * ∑' full, fulls full *
      choose key mask full selected * weight key mask full selected := by
  have reorder := selectedSumOrder.symm.tsum_eq
    (fun coin : Key × Mask × Full × Selected =>
      keys coin.1 * (masks coin.2.1 * (fulls coin.2.2.1 *
        (choose coin.1 coin.2.1 coin.2.2.1 coin.2.2.2 * weight coin.1 coin.2.1 coin.2.2.1 coin.2.2.2))))
  simp only [← ENNReal.tsum_mul_left]
  simpa only [ENNReal.tsum_prod', selectedSumOrder, Equiv.coe_fn_symm_mk, mul_assoc] using reorder.symm

end
end Kriterion.ArgoMAC.Security
