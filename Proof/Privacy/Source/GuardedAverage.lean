import Proof.Privacy.Source.PadRestrictedKeyMass
namespace Kriterion.ArgoMAC.Security
open Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem uniform_pair_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A × B → ℝ≥0∞) :
    (∑' pair, (PMF.uniformOfFintype (A × B)) pair * weight pair) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight (first, second) := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

private theorem weighted_swap {A B : Type*} (first : PMF A) (second : PMF B)
    (weight : A → B → ℝ≥0∞) :
    (∑' a, first a * ∑' b, second b * weight a b) =
      ∑' b, second b * ∑' a, first a * weight a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro b
  apply tsum_congr
  intro a
  ac_rfl

private theorem ite_tsum {A : Type*} (p : Prop) (f : A → ℝ≥0∞) :
    (if p then ∑' a, f a else 0) = ∑' a, if p then f a else 0 := by
  by_cases condition : p <;> simp [condition]

private theorem ite_mul_zero (p : Prop) (a b : ℝ≥0∞) :
    (if p then a * b else 0) = a * (if p then b else 0) := by
  by_cases condition : p <;> simp [condition]

/-- The nested guarded source average is one normalized product event. -/
theorem guarded_average_factor {A B C H : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype H]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty H]
    (selected : B → Prop) (compatible : A → H → Prop)
    (guard : B → C → Prop) (tag : A → B → C → Prop) (factor : ℝ≥0∞) :
    (∑' coin : A × B, (PMF.uniformOfFintype (A × B)) coin *
      if selected coin.2 then
        (∑' hash : H, (PMF.uniformOfFintype H) hash *
          if compatible coin.1 hash then factor *
            (∑' target : C, (PMF.uniformOfFintype C) target *
              if guard coin.2 target then (if tag coin.1 coin.2 target then 1 else 0) else 0)
          else 0) else 0) =
    factor * ∑' hash : H, (PMF.uniformOfFintype H) hash *
      (PMF.uniformOfFintype (A × (B × C))).toOuterMeasure
        {coin | selected coin.2.1 ∧ tag coin.1 coin.2.1 coin.2.2 ∧
          compatible coin.1 hash ∧ guard coin.2.1 coin.2.2} := by
  simp_rw [ite_tsum, ite_mul_zero]
  rw [weighted_swap]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro hash
  rw [mul_left_comm factor]
  apply congrArg (fun mass => (PMF.uniformOfFintype H) hash * mass)
  rw [uniform_pair_weight, PMF.toOuterMeasure_apply]
  rw [show (∑' coin : A × (B × C),
      {coin | selected coin.2.1 ∧ tag coin.1 coin.2.1 coin.2.2 ∧ compatible coin.1 hash ∧ guard coin.2.1 coin.2.2}.indicator
        (PMF.uniformOfFintype (A × (B × C))) coin) =
      ∑' coin : A × (B × C), (PMF.uniformOfFintype (A × (B × C))) coin *
        if selected coin.2.1 ∧ tag coin.1 coin.2.1 coin.2.2 ∧ compatible coin.1 hash ∧ guard coin.2.1 coin.2.2 then 1 else 0 by
    apply tsum_congr
    intro coin
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split <;> simp_all]
  rw [uniform_pair_weight]
  simp_rw [uniform_pair_weight]
  simp only [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  simp_rw [ite_tsum]
  simp only [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro c
  by_cases first : selected b <;> by_cases second : compatible a hash <;>
    by_cases third : guard b c <;> by_cases fourth : tag a b c <;>
    simp [first, second, third, fourth, mul_assoc, mul_left_comm, mul_comm]

end
end Kriterion.ArgoMAC.Security
