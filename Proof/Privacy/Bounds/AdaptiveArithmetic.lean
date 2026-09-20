import Proof.Privacy.Bounds.Security

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography Cryptography.Assumptions

/-- This count uses two blocks per hash-density bound and six per pad-density bound. -/
def adaptiveConstantCount : Nat :=
  9 * (Pipeline.pointDigitAdaptorsPerOutput * coordinateBitCount * Pipeline.digitsPerBucket ^ 2 +
    Pipeline.curveDigitAdaptorCount * coordinateBitCount) + bitAdaptorEvaluationCount + 508 + 2

/-- This count includes separate active and inactive query losses. -/
def adaptiveQueryCount : Nat := 9 * Pipeline.digitsPerBucket + 4 + 1

/-- This arithmetic envelope includes collisions, rounding, linking, and tape restrictions. -/
noncomputable def adaptiveErrorEnvelope (queries : Nat) : ℝ :=
  ((adaptiveConstantCount + adaptiveQueryCount * queries : Nat) : ℝ) / (2 : ℝ) ^ blockBits

/-- The conservative error envelope fits the existing 100-bit work obligation. -/
theorem adaptiveErrorEnvelope_has100Bits :
    ConcreteBound 100 permutationWork adaptiveErrorEnvelope := by
  intro queries
  have countBound : adaptiveConstantCount + adaptiveQueryCount * queries ≤
      permutationWork queries * 2 ^ 28 := by
    change 227454970 + 824 * queries ≤ max queries 1 * 268435456
    omega
  change (((adaptiveConstantCount + adaptiveQueryCount * queries : Nat) : ℝ) /
      (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 ≤ ((permutationWork queries : Nat) : ℝ)
  calc
    _ = ((adaptiveConstantCount + adaptiveQueryCount * queries : Nat) : ℝ) / (2 : ℝ) ^ 28 := by
      norm_num [div_eq_mul_inv]
      ring
    _ ≤ ((permutationWork queries : Nat) : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 28)).mpr
      exact_mod_cast countBound

set_option exponentiation.threshold 400

/-- The exact field modulus gives a pad density below 5.3 inverse blocks. -/
theorem padDensity_le_fiftyThreeTenths [Fintype Block] :
    (Fintype.card Block : ENNReal) / baseFieldModulus ≤
      (53 / 10) / (2 : ENNReal) ^ 128 := by
  have card : Fintype.card Block = 2 ^ 128 := by
    exact (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card]
  apply (ENNReal.toReal_le_toReal (by norm_num [baseFieldModulus, hashLiftQuotientCount]; finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, baseFieldModulus]

/-- The original six-block bound follows from the tighter field bound. -/
theorem padDensity_le_six [Fintype Block] :
    (Fintype.card Block : ENNReal) / baseFieldModulus ≤
      6 / (2 : ENNReal) ^ 128 := by
  apply padDensity_le_fiftyThreeTenths.trans
  apply ENNReal.div_le_div_right
  apply (ENNReal.div_le_iff (by norm_num) (by finiteness)).mpr
  norm_num

/-- The complete hash fibers give a density below 1.001 inverse blocks. -/
theorem hashDensity_le_thousandOneThousandths [Fintype Block] :
    (Fintype.card Block : ENNReal) ^ 2 /
      (baseFieldModulus * hashLiftQuotientCount : Nat) ≤
        (1001 / 1000) / (2 : ENNReal) ^ 128 := by
  have card : Fintype.card Block = 2 ^ 128 := by
    exact (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card]
  apply (ENNReal.toReal_le_toReal (by norm_num [baseFieldModulus, hashLiftQuotientCount]; finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, baseFieldModulus, hashLiftQuotientCount]

/-- The original two-block bound follows from the tighter hash bound. -/
theorem hashDensity_le_two [Fintype Block] :
    (Fintype.card Block : ENNReal) ^ 2 /
      (baseFieldModulus * hashLiftQuotientCount : Nat) ≤
        2 / (2 : ENNReal) ^ 128 := by
  apply hashDensity_le_thousandOneThousandths.trans
  apply ENNReal.div_le_div_right
  apply (ENNReal.div_le_iff (by norm_num) (by finiteness)).mpr
  norm_num

/-- One field-mask loss fits one inverse block count. -/
theorem fieldMaskLoss_le_block :
    (1 : ℝ) / baseFieldModulus ≤ 1 / (2 : ℝ) ^ 128 := by
  norm_num [baseFieldModulus]

/-- Whole-circuit hash rounding fits one inverse block count per gate. -/
theorem circuitHashRounding_le_blocks :
    (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 ≤
      278638 / (2 : ℝ) ^ 128 := by
  norm_num [baseFieldModulus]

/-- Every Boolean decision advantage is at most one. -/
theorem decisionAdvantage_le_one (real ideal : PMF Bool) : advantage real ideal ≤ 1 := by
  simpa only [advantage, PMF.probOutput_eq_apply] using
    (abs_probOutput_toReal_sub_le_tvDist real ideal).trans (tvDist_le_one real ideal)

/-- Large query budgets satisfy the work metric from the unit advantage bound. -/
theorem largeBudget_has100Bits (real ideal : PMF Bool) (queries : Nat)
    (large : 2 ^ 100 ≤ queries) :
    WorkPerAdvantage 100 (queries + 1) (advantage real ideal) := by
  unfold WorkPerAdvantage
  calc
    _ ≤ 1 * (2 : ℝ) ^ 100 := mul_le_mul_of_nonneg_right (decisionAdvantage_le_one real ideal) (by positivity)
    _ ≤ ((queries + 1 : Nat) : ℝ) := by
      simp only [one_mul]
      exact_mod_cast large.trans (Nat.le_succ queries)

/-- The concrete adaptive envelope gives the required work metric. -/
theorem adaptiveEnvelope_has100Bits {error : ℝ} (queries : Nat)
    (bound : error ≤ adaptiveErrorEnvelope queries) :
    WorkPerAdvantage 100 (queries + 1) error := by
  unfold WorkPerAdvantage
  apply (mul_le_mul_of_nonneg_right bound (by positivity : 0 ≤ (2 : ℝ) ^ 100)).trans
  apply (adaptiveErrorEnvelope_has100Bits queries).trans
  exact_mod_cast (show permutationWork queries ≤ queries + 1 from by
    unfold permutationWork
    omega)

/-- Every small work budget fits all five point-gate slots and the external queries. -/
theorem smallBudget_slots_fit [Fintype Block] (queries : Nat) (small : queries < 2 ^ 100) :
    5 * 91 + queries ≤ Fintype.card Block := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card]
  norm_num at small ⊢
  omega

/-- The checked collision, query, linking, and source losses fit the adaptive envelope. -/
theorem adaptiveLossSum_le_envelope (before queries : Nat) (beforeLe : before ≤ queries) :
    (224668080 : ℝ) / 2 ^ 128 + 182 * before / 2 ^ 128 + 182 * queries / 2 ^ 128 +
      queries / (baseFieldModulus : ℝ) + (508 + 4 * queries) / 2 ^ 128 + 1 / baseFieldModulus +
      2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) ≤
        adaptiveErrorEnvelope queries := by
  have hidden : (queries : ℝ) / baseFieldModulus ≤ queries / (2 : ℝ) ^ 128 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left fieldMaskLoss_le_block (Nat.cast_nonneg queries)
  have offset : (2 : ℝ) ^ (-240 : ℤ) ≤ 1 / (2 : ℝ) ^ 128 := by norm_num
  have prefixBound : (before : ℝ) ≤ queries := by exact_mod_cast beforeLe
  calc
    _ ≤ (224668080 : ℝ) / 2 ^ 128 + 182 * before / 2 ^ 128 + 182 * queries / 2 ^ 128 +
        queries / (2 : ℝ) ^ 128 + (508 + 4 * queries) / 2 ^ 128 + 1 / 2 ^ 128 + 2 * (278638 / 2 ^ 128) +
        1 / 2 ^ 128 := by linarith [circuitHashRounding_le_blocks, fieldMaskLoss_le_block]
    _ ≤ adaptiveErrorEnvelope queries := by
      change _ ≤ ((227454970 + 824 * queries : Nat) : ℝ) / (2 : ℝ) ^ 128
      push_cast
      norm_num
      linarith [Nat.cast_nonneg (α := ℝ) queries]

end Kriterion.ArgoMAC.Security
