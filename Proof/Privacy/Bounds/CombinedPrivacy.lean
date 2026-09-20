import Proof.Privacy.Bounds.AdaptiveArithmetic

namespace Kriterion.ArgoMAC.Security
open Cryptography.Assumptions

/-- The two simulation distances have a combined bound of two. -/
theorem combinedAdvantage_le_two (real ideal machine : PMF Bool) :
    advantage real ideal + advantage ideal machine ≤ 2 := by
  linarith [decisionAdvantage_le_one real ideal, decisionAdvantage_le_one ideal machine]

/-- Large declared query budgets satisfy the complete combined privacy allowance. -/
theorem largeBudget_combinedPrivacy (real ideal machine : PMF Bool) (queries : Nat)
    (large : 2 ^ 101 ≤ queries) :
    WorkPerAdvantage 100 (queries + 1)
      (advantage real ideal + advantage ideal machine) := by
  unfold WorkPerAdvantage
  calc
    _ ≤ 2 * (2 : ℝ) ^ 100 := mul_le_mul_of_nonneg_right
      (combinedAdvantage_le_two real ideal machine) (by positivity)
    _ = ((2 ^ 101 : Nat) : ℝ) := by norm_num
    _ ≤ ((queries + 1 : Nat) : ℝ) := by
      exact_mod_cast large.trans (Nat.le_succ queries)

end Kriterion.ArgoMAC.Security
