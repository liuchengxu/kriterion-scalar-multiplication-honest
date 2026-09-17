import Proof.Privacy.Bounds.AdaptiveArithmetic
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal

/-- Two relative exclusions pay the sum of their losses once. -/
theorem relativeLoss_product (first second : ℝ≥0∞) :
    1 - (first + second) ≤ (1 - first) * (1 - second) := by
  rw [ENNReal.mul_sub (fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self),
    mul_one, tsub_add_eq_tsub_tsub]
  apply tsub_le_tsub_left
  calc
    (1 - first) * second ≤ 1 * second := mul_le_mul_left tsub_le_self second
    _ = second := one_mul _

/-- The invalid fixed and EncPRF factors use one pad loss. -/
theorem invalidRelativeLoss_product (queries : Nat) :
    1 - (((186 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 + 508 / (2 : ℝ≥0∞) ^ 128) ≤
      (1 - (((182 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 + 508 / (2 : ℝ≥0∞) ^ 128)) *
      (1 - ((4 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128) := by
  have split : (((186 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 + 508 / (2 : ℝ≥0∞) ^ 128) =
      (((182 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 + 508 / (2 : ℝ≥0∞) ^ 128) +
        ((4 * queries : Nat) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [show 186 * queries = 182 * queries + 4 * queries by omega, Nat.cast_add, ENNReal.add_div]
    exact add_right_comm _ _ _
  rw [split]
  exact relativeLoss_product _ _

/-- The source flags, relative factors, and hidden-key exclusions fit the current envelope. -/
theorem invalidCombinedLoss_le_envelope (before queries : Nat) (beforeLe : before ≤ queries) :
    ((224668080 : ℝ) / 2 ^ 128 + 182 * before / 2 ^ 128) +
      ((186 * queries + 508) / 2 ^ 128 + (queries + 1) / (baseFieldModulus : ℝ)) +
      2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) ≤
        adaptiveErrorEnvelope queries := by
  have bound := adaptiveLossSum_le_envelope before queries beforeLe
  convert bound using 1
  ring

end Kriterion.ArgoMAC.Security
