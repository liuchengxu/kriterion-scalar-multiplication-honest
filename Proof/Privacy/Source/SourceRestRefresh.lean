import Proof.Privacy.Source.RealSourceSum

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- This permutation exchanges the retained nonfixed functions with independent functions. -/
def sourceRestNonfixedSwap :
    GarblingSourceRest × ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle) ≃
    GarblingSourceRest × ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle) where
  toFun pair := ({pair.1 with encPRFOracle := pair.2.1, hashOracle := pair.2.2},
    pair.1.encPRFOracle, pair.1.hashOracle)
  invFun pair := ({pair.1 with encPRFOracle := pair.2.1, hashOracle := pair.2.2},
    pair.1.encPRFOracle, pair.1.hashOracle)
  left_inv pair := by rcases pair with ⟨⟨_, _, _, _⟩, _, _⟩; rfl
  right_inv pair := by rcases pair with ⟨⟨_, _, _, _⟩, _, _⟩; rfl

private theorem uniform_pair_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- Refreshing the nonfixed functions preserves every normalized retained-source weight. -/
theorem sourceRest_nonfixed_refresh [Fintype Block] [Nonempty GarblingSourceRest]
    (weight : GarblingSourceRest → ℝ≥0∞) :
    (∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
      ∑' nonfixed : (PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle,
        (PMF.uniformOfFintype ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) nonfixed *
        weight {rest with encPRFOracle := nonfixed.1, hashOracle := nonfixed.2}) =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest * weight rest := by
  have reindex := sourceRestNonfixedSwap.tsum_eq
    (fun pair => (PMF.uniformOfFintype (GarblingSourceRest ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle))) pair * weight pair.1)
  have uniformSwap (pair : GarblingSourceRest ×
      ((PermutationOracle EncPRF.PermutationIndex Block) × EncPRF.HashOracle)) :
      (PMF.uniformOfFintype _) (sourceRestNonfixedSwap pair) =
        (PMF.uniformOfFintype _) pair := by simp only [PMF.uniformOfFintype_apply]
  simp only [uniformSwap] at reindex
  rw [uniform_pair_weight, uniform_pair_weight] at reindex
  simpa only [sourceRestNonfixedSwap, Equiv.coe_fn_mk, ENNReal.tsum_mul_right,
    PMF.tsum_coe, one_mul] using reindex

end
end Kriterion.ArgoMAC.Security
