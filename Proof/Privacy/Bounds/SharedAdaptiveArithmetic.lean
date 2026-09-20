import Proof.Privacy.Bounds.AdaptiveArithmetic

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions

/-- The shared source pays its point-row and label constants once.

The point-row term is the tight bound `pointBranchCollision_mass_le_tight`
reads off the actual row sources, the two per-query coefficients are the
shared source's own 364-inverse-block prequery constant and its 4-block curve
companion, and the label constant is the shared cross-branch count plus the
508 coordinate labels. -/
theorem sharedAdaptiveLossSum_le_envelope (before queries : Nat) (beforeLe : before ≤ queries) :
    ((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
      ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / (baseFieldModulus : ℝ)) +
      2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) ≤
        adaptiveErrorEnvelope queries := by
  have hidden : ((queries : ℝ) + 1) / baseFieldModulus ≤ (queries + 1) / (2 : ℝ) ^ 128 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left fieldMaskLoss_le_block (by positivity : 0 ≤ (queries : ℝ) + 1)
  have offset : (2 : ℝ) ^ (-240 : ℤ) ≤ 1 / (2 : ℝ) ^ 128 := by norm_num
  have prefixBound : (before : ℝ) ≤ queries := by exact_mod_cast beforeLe
  calc
    _ ≤ ((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
        ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / 2 ^ 128) +
        2 * (278638 / 2 ^ 128) + 1 / 2 ^ 128 := by
      linarith [circuitHashRounding_le_blocks]
    _ ≤ adaptiveErrorEnvelope queries := by
      change _ ≤ ((227454970 + 824 * queries : Nat) : ℝ) / (2 : ℝ) ^ 128
      push_cast
      norm_num
      linarith [Nat.cast_nonneg (α := ℝ) queries]

/-- The shared source loss fits the required 100-bit work allowance. -/
theorem sharedAdaptiveLoss_has100Bits (before queries : Nat) (beforeLe : before ≤ queries) :
    WorkPerAdvantage 100 (queries + 1)
      (((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
        ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / (baseFieldModulus : ℝ)) +
        2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ)) :=
  adaptiveEnvelope_has100Bits queries (sharedAdaptiveLossSum_le_envelope before queries beforeLe)

/-- The complete source proof pays three rounding losses and each collision constant once. -/
theorem sharedAdaptiveThreeRoundingLossSum_le_envelope (before queries : Nat) (beforeLe : before ≤ queries) :
    ((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
      ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / (baseFieldModulus : ℝ)) +
      3 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) ≤
        adaptiveErrorEnvelope queries := by
  have hidden : ((queries : ℝ) + 1) / baseFieldModulus ≤ (queries + 1) / (2 : ℝ) ^ 128 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left fieldMaskLoss_le_block (by positivity : 0 ≤ (queries : ℝ) + 1)
  have offset : (2 : ℝ) ^ (-240 : ℤ) ≤ 1 / (2 : ℝ) ^ 128 := by norm_num
  have prefixBound : (before : ℝ) ≤ queries := by exact_mod_cast beforeLe
  calc
    _ ≤ ((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
        ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / 2 ^ 128) +
        3 * (278638 / 2 ^ 128) + 1 / 2 ^ 128 := by
      linarith [circuitHashRounding_le_blocks]
    _ ≤ adaptiveErrorEnvelope queries := by
      change _ ≤ ((227454970 + 824 * queries : Nat) : ℝ) / (2 : ℝ) ^ 128
      push_cast
      norm_num
      linarith [Nat.cast_nonneg (α := ℝ) queries]

/-- The complete three-rounding source loss fits the required 100-bit work allowance. -/
theorem sharedAdaptiveThreeRoundingLoss_has100Bits (before queries : Nat) (beforeLe : before ≤ queries) :
    WorkPerAdvantage 100 (queries + 1)
      (((169786660680 / 1000 : ℝ) / 2 ^ 128 + 364 * before / 2 ^ 128) +
        ((54691280 + 368 * queries) / 2 ^ 128 + (queries + 1) / (baseFieldModulus : ℝ)) +
        3 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ)) :=
  adaptiveEnvelope_has100Bits queries (sharedAdaptiveThreeRoundingLossSum_le_envelope before queries beforeLe)

end Kriterion.ArgoMAC.Security
