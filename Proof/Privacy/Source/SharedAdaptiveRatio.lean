import Proof.Privacy.Source.AdaptivePermutationRatio

namespace Kriterion.ArgoMAC.Security
open Cryptography
open scoped ENNReal
noncomputable section

/-- A shared slot contains active programming and independent hidden assignments. -/
def mixedIdealSlotFactor (N active hidden prior residual : Nat) : ENNReal :=
  ((N : ENNReal) ^ hidden)⁻¹ * activeIdealSlotFactor N active prior residual

/-- Both branch counts fit in one exact real permutation factor. -/
theorem mixedIdealSlotFactor_le (N active hidden prior residual : Nat)
    (positive : 0 < N) (priorFits : active + prior ≤ N)
    (residualFits : active + hidden + residual ≤ N) :
    mixedIdealSlotFactor N active hidden prior residual ≤
      ((N - (active + hidden + residual)).factorial : ENNReal) / N.factorial := by
  have activeBound := mul_le_mul_right
    (activeIdealSlotFactor_le N active prior residual positive priorFits)
    (((N : ENNReal) ^ hidden)⁻¹)
  apply activeBound.trans
  have hiddenBound := factorial_ratio_ge_inverse_power N hidden (active + residual)
    positive (by omega)
  have count : hidden + (active + residual) = active + hidden + residual := by omega
  simpa only [mixedIdealSlotFactor, count, ← mul_div_assoc] using hiddenBound

/-- The shared product counts each active and hidden assignment in its public slot. -/
def sharedAdaptivePermutationFactor {Index : Type} [Fintype Index]
    (N : Nat) (active hidden prior residual : Index → Nat) : ENNReal :=
  ∏ index, mixedIdealSlotFactor N (active index) (hidden index) (prior index) (residual index)

/-- The mixed product replaces the old partition into active and inactive slots. -/
theorem sharedAdaptivePermutationFactor_le {Index : Type} [Fintype Index]
    (N : Nat) (active hidden prior residual : Index → Nat)
    (positive : 0 < N) (priorFits : ∀ index, active index + prior index ≤ N)
    (residualFits : ∀ index, active index + hidden index + residual index ≤ N) :
    sharedAdaptivePermutationFactor N active hidden prior residual ≤
      ∏ index, ((N - (active index + hidden index + residual index)).factorial : ENNReal) /
        N.factorial := by
  apply Finset.prod_le_prod'
  intro index _
  exact mixedIdealSlotFactor_le N (active index) (hidden index) (prior index)
    (residual index) positive (priorFits index) (residualFits index)

end
end Kriterion.ArgoMAC.Security
