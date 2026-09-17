import Proof.Privacy.Simulator.SimulatorFinitePrivacy

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions OperationalOracle
open SimulatorSampling BoundedIntegerSampling
namespace SimulatorMachine
noncomputable section

/-- This relation retains a common part of two total output distributions. -/
def TotalLaw {A : Type} (attempts count : Nat) (exact total : PMF A) : Prop :=
  ∀ value, retained attempts ^ count * exact value ≤ total value

/-- A total fallback preserves every successful output of the aborting sampler. -/
theorem CutoffLaw.total {A : Type} {attempts count : Nat}
    {exact : PMF A} {finite : PMF (Option A)} {total : PMF A}
    (law : CutoffLaw attempts count exact finite)
    (dominates : ∀ value, finite (some value) ≤ total value) :
    TotalLaw attempts count exact total :=
  fun value => (law.1 value).trans (dominates value)

/-- An unchanged distribution consumes no bounded integer draws. -/
theorem TotalLaw.exact {A : Type} (attempts : Nat) (distribution : PMF A) :
    TotalLaw attempts 0 distribution distribution := by
  intro value
  simp

/-- A larger draw budget preserves the relation. -/
theorem TotalLaw.weaken {A : Type} {attempts first second : Nat}
    {exact total : PMF A} (law : TotalLaw attempts first exact total)
    (bounded : first ≤ second) : TotalLaw attempts second exact total := by
  intro value
  exact (mul_le_mul_left (pow_le_pow_right_of_le_one'
    (tsub_le_self : retained attempts ≤ 1) bounded) _).trans (law value)

/-- Adaptive composition adds the draw budgets. -/
theorem TotalLaw.bind {A B : Type} {attempts first second : Nat}
    {source totalSource : PMF A} {next totalNext : A → PMF B}
    (left : TotalLaw attempts first source totalSource)
    (right : ∀ item, TotalLaw attempts second (next item) (totalNext item)) :
    TotalLaw attempts (first + second) (source.bind next) (totalSource.bind totalNext) := by
  intro value
  rw [PMF.bind_apply, PMF.bind_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro item
  calc
    retained attempts ^ (first + second) * (source item * next item value) =
        (retained attempts ^ first * source item) *
          (retained attempts ^ second * next item value) := by rw [pow_add]; ac_rfl
    _ ≤ _ := mul_le_mul' (left item) (right item value)

/-- Private adversary randomness adds no simulator draw loss. -/
theorem TotalLaw.sample {A B : Type} {attempts count : Nat}
    (source : PMF A) {next totalNext : A → PMF B}
    (law : ∀ item, TotalLaw attempts count (next item) (totalNext item)) :
    TotalLaw attempts count (source.bind next) (source.bind totalNext) := by
  simpa only [Nat.zero_add] using (TotalLaw.exact attempts source).bind law

/-- A deterministic observation preserves the relation. -/
theorem TotalLaw.map {A B : Type} {attempts count : Nat} {exact total : PMF A}
    (law : TotalLaw attempts count exact total) (observe : A → B) :
    TotalLaw attempts count (exact.map observe) (total.map observe) := by
  exact law.bind (fun value => TotalLaw.exact attempts (PMF.pure (observe value)))

/-- The common output mass bounds the probability lost at each output. -/
theorem TotalLaw.point_error {A : Type} {attempts count : Nat}
    {exact total : PMF A} (law : TotalLaw attempts count exact total) (value : A) :
    (exact value).toReal - (total value).toReal ≤
      (count : ℝ) * (2 : ℝ)⁻¹ ^ attempts := by
  have retainedLe : retained attempts ^ count ≤ 1 :=
    pow_le_one₀ zero_le (tsub_le_self : retained attempts ≤ 1)
  have lower := ENNReal.toReal_mono (total.apply_ne_top _) (law value)
  have pointLe := ENNReal.toReal_mono ENNReal.one_ne_top (exact.coe_le_one value)
  have factorLe := ENNReal.toReal_mono ENNReal.one_ne_top retainedLe
  have loss := loss_pow_le ((2 : ENNReal)⁻¹ ^ attempts)
    (pow_le_one₀ zero_le (by norm_num)) count
  have realLoss := ENNReal.toReal_mono (by finiteness) loss
  change (1 - retained attempts ^ count).toReal ≤ _ at realLoss
  rw [ENNReal.toReal_sub_of_le retainedLe ENNReal.one_ne_top] at realLoss
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
      at lower pointLe factorLe realLoss ⊢
  nlinarith

private theorem bool_mass (distribution : PMF Bool) :
    (distribution false).toReal + (distribution true).toReal = 1 := by
  have mass := distribution.tsum_coe
  rw [tsum_fintype] at mass
  simp only [Fintype.sum_bool] at mass
  have realMass := congrArg ENNReal.toReal mass
  rw [ENNReal.toReal_add (distribution.apply_ne_top _) (distribution.apply_ne_top _)] at realMass
  simpa only [ENNReal.toReal_one, add_comm] using realMass

/-- A total fallback changes the decision probability by at most the retry loss. -/
theorem TotalLaw.advantage {attempts count : Nat} {exact total : PMF Bool}
    (law : TotalLaw attempts count exact total) :
    advantage exact total ≤ (count : ℝ) * (2 : ℝ)⁻¹ ^ attempts := by
  have trueBound := law.point_error true
  have falseBound := law.point_error false
  have exactMass := bool_mass exact
  have totalMass := bool_mass total
  change |(exact true).toReal - (total true).toReal| ≤ _
  apply abs_le.mpr
  constructor <;> linarith

end
end SimulatorMachine
end Kriterion.ArgoMAC.Security
