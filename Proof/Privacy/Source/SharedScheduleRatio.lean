import Proof.Privacy.Source.SharedAdaptiveRatio
import Proof.Privacy.Distribution.SharedProgramQueryMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The source and two transcript phases factor into the mixed shared-slot ratio. -/
theorem sharedSourceTranscriptFactor_eq {Index : Type} [Fintype Index]
    (N : Nat) (active hidden prior residual : Index → Nat) :
    (∏ index, ((N : ENNReal) ^ (active index + hidden index))⁻¹) *
      (∏ index, ((N - prior index).factorial : ENNReal) / N.factorial) *
      ((∏ index, ((N - (active index + residual index)).factorial : ENNReal) / N.factorial) /
        (∏ index, ((N - (active index + prior index)).factorial : ENNReal) / N.factorial)) =
      sharedAdaptivePermutationFactor N active hidden prior residual := by
  classical
  rw [← ENNReal.prod_div_distrib_of_ne_top (fun index _ =>
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))), ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro index _
  unfold mixedIdealSlotFactor activeIdealSlotFactor
  rw [pow_add, ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
    (Or.inl (ENNReal.natCast_ne_top _)), inv_inv]
  calc
    _ = (((N : ENNReal) ^ hidden index)⁻¹ * ((N : ENNReal) ^ active index)⁻¹ *
        ((N - prior index).factorial : ENNReal) * (N.factorial : ENNReal)⁻¹ *
        ((N - (active index + residual index)).factorial : ENNReal) *
        ((N - (active index + prior index)).factorial : ENNReal)⁻¹) *
        ((N.factorial : ENNReal) * (N.factorial : ENNReal)⁻¹) := by ring
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))
        (ENNReal.natCast_ne_top _), mul_one]
      ring

/-- Both transcript phases and the full shared source fit the real permutation factor. -/
theorem sharedSourceTranscriptFactor_le {Index : Type} [Fintype Index]
    (N : Nat) (active hidden prior residual : Index → Nat)
    (positive : 0 < N) (priorFits : ∀ index, active index + prior index ≤ N)
    (residualFits : ∀ index, active index + hidden index + residual index ≤ N) :
    (∏ index, ((N : ENNReal) ^ (active index + hidden index))⁻¹) *
      (∏ index, ((N - prior index).factorial : ENNReal) / N.factorial) *
      ((∏ index, ((N - (active index + residual index)).factorial : ENNReal) / N.factorial) /
        (∏ index, ((N - (active index + prior index)).factorial : ENNReal) / N.factorial)) ≤
      ∏ index, ((N - (active index + hidden index + residual index)).factorial : ENNReal) /
        N.factorial := by
  rw [sharedSourceTranscriptFactor_eq]
  exact sharedAdaptivePermutationFactor_le N active hidden prior residual positive priorFits residualFits

end
end Kriterion.ArgoMAC.Security
