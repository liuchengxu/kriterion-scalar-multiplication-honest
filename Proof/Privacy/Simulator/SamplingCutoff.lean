import Proof.Privacy.Simulator.SimulatorSampling
import Proof.Privacy.Simulator.BoundedIntegerSampling

namespace Kriterion.ArgoMAC.Security
open scoped ENNReal
open BoundedIntegerSampling
namespace BoundedIntegerSampling

/-- The bit program executes its continuation after the first result. -/
def BitCode.bind {A B : Type} (source : BitCode A) (next : A → BitCode B) : BitCode B :=
  match source with
  | .pure value => next value
  | .bits width branch => .bits width fun value => (branch value).bind next

theorem BitCode.bind_law {A B : Type} (source : BitCode A) (next : A → BitCode B) :
    (source.bind next).law = source.law.bind (fun value => (next value).law) := by
  induction source with
  | pure => simp [BitCode.bind, BitCode.law]
  | bits width branch ih => simp only [BitCode.bind, BitCode.law, ih, PMF.bind_bind]

/-- The bit interpreter counts the bits in both executed programs. -/
theorem BitCode.bind_run {A B State : Type}
    (random : (width : Nat) → State → Fin (2 ^ width) × State)
    (source : BitCode A) (next : A → BitCode B) (state : State) :
    (source.bind next).run random state =
      let first := source.run random state
      let second := (next first.1.1).run random first.1.2
      (second.1, first.2 + second.2) := by
  induction source generalizing state with
  | pure => simp [BitCode.bind, BitCode.run]
  | bits width branch ih =>
      simp only [BitCode.bind, BitCode.run, ih, Nat.add_assoc]

end BoundedIntegerSampling
namespace SimulatorSampling

/-- The finite sampler stops when a bounded integer draw reaches its retry limit. -/
def Code.cutoff {A : Type} {count : Nat} (attempts : Nat) : Code A count → BitCode (Option A)
  | .pure value => .pure (some value)
  | .draw size _ => BoundedIntegerSampling.cutoff size attempts
  | .bind source next => (source.cutoff attempts).bind fun value =>
      match value with
      | none => .pure none
      | some value => (next value).cutoff attempts

private theorem tsum_option {A : Type} (f : Option A → ENNReal) :
    (∑' value, f value) = f none + ∑' value, f (some value) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} A).symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp [add_comm]

private theorem option_law {A B : Type} (next : A → BitCode (Option B)) (value : Option A) :
    (match value with | none => BitCode.pure none | some item => next item).law =
      match value with | none => PMF.pure none | some item => (next item).law := by
  cases value <;> rfl

private theorem bind_option_some {A B : Type} (source : PMF (Option A))
    (next : A → PMF (Option B)) (value : B) :
    (source.bind (fun result => match result with
      | none => PMF.pure none
      | some item => next item)) (some value) =
      ∑' item, source (some item) * next item (some value) := by
  rw [PMF.bind_apply, tsum_option]
  simp

/-- A finite retry limit retains at least this mass in each bounded draw. -/
noncomputable def retained (attempts : Nat) : ENNReal := 1 - (2 : ENNReal)⁻¹ ^ attempts

/-- Every successful result keeps a uniform fraction of its exact probability. -/
theorem Code.cutoff_lower {A : Type} {count : Nat} (attempts : Nat)
    (code : Code A count) (value : A) :
    retained attempts ^ count * code.law value ≤ (code.cutoff attempts).law (some value) := by
  classical
  induction code with
  | pure item =>
      simp only [Code.cutoff, Code.law, BitCode.law, pow_zero, one_mul, PMF.pure_apply, Option.some.injEq]
      exact le_rfl
  | draw size positive =>
      simp only [Code.cutoff, Code.law, PMF.uniformOfFintype_apply, Fintype.card_fin, pow_one]
      rw [cutoff_success_submass size positive]
      exact mul_le_mul_left (tsub_le_tsub_left
        (pow_le_pow_left' (rejection_le_half size positive) attempts) 1) _
  | @bind A B first second source next ihSource ihNext =>
      simp only [Code.cutoff, Code.law, BitCode.bind_law, option_law]
      rw [bind_option_some, PMF.bind_apply, pow_add, ← ENNReal.tsum_mul_left]
      apply ENNReal.tsum_le_tsum
      intro item
      calc
        (retained attempts ^ first * retained attempts ^ second) *
            (source.law item * (next item).law value) =
            (retained attempts ^ first * source.law item) *
              (retained attempts ^ second * (next item).law value) := by ac_rfl
        _ ≤ _ := mul_le_mul' (ihSource item) (ihNext item value)

/-- The finite retry sampler never adds probability mass to a successful result. -/
theorem Code.cutoff_upper {A : Type} {count : Nat} (attempts : Nat)
    (code : Code A count) (value : A) :
    (code.cutoff attempts).law (some value) ≤ code.law value := by
  classical
  induction code with
  | pure item => simp [Code.cutoff, Code.law, BitCode.law, PMF.pure_apply, Option.some.injEq]
  | draw size positive =>
      simp only [Code.cutoff, Code.law, PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [cutoff_success_submass size positive]
      exact (mul_le_mul_left (tsub_le_self : (1 : ENNReal) - rejection size ^ attempts ≤ 1) _).trans_eq
        (one_mul _)
  | @bind A B first second source next ihSource ihNext =>
      simp only [Code.cutoff, Code.law, BitCode.bind_law, option_law]
      rw [bind_option_some, PMF.bind_apply]
      exact ENNReal.tsum_le_tsum fun item => mul_le_mul' (ihSource item) (ihNext item value)

/-- The complete private sampler has an explicit failure-probability bound. -/
theorem Code.cutoff_failure {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    (code.cutoff attempts).law none ≤ 1 - retained attempts ^ count := by
  have total := (code.cutoff attempts).law.tsum_coe
  rw [tsum_option] at total
  have lower : retained attempts ^ count ≤ ∑' value, (code.cutoff attempts).law (some value) := by
    calc
      retained attempts ^ count = retained attempts ^ count * ∑' value, code.law value := by
        rw [code.law.tsum_coe, mul_one]
      _ = ∑' value, retained attempts ^ count * code.law value := ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum fun value => code.cutoff_lower attempts value
  exact (ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top total).le.trans (tsub_le_tsub_left lower 1)

/-- The finite private sampler reads at most 257 bits per allowed retry and draw. -/
theorem Code.cutoff_bit_bound {A State : Type} {count : Nat}
    (random : (width : Nat) → State → Fin (2 ^ width) × State)
    (attempts : Nat) (code : Code A count) (bounded : code.DrawSizeLe (2 ^ 256)) (state : State) :
    ((code.cutoff attempts).run random state).2 ≤ count * (257 * attempts) := by
  induction code generalizing state with
  | pure => simp [Code.cutoff, BitCode.run]
  | draw size positive =>
      simpa only [Code.cutoff, one_mul] using
        cutoff_run_bits_le_257 random size positive bounded attempts state
  | @bind A B first second source next ihSource ihNext =>
      obtain ⟨left, right⟩ := bounded
      have firstBound := ihSource left state
      simp only [Code.cutoff, BitCode.bind_run]
      split
      · simpa only [BitCode.run, Nat.add_zero] using
          firstBound.trans (Nat.mul_le_mul_right _ (Nat.le_add_right first second))
      · rename_i item same
        have secondBound := ihNext item (right item) ((source.cutoff attempts).run random state).1.2
        exact (Nat.add_le_add firstBound secondBound).trans_eq (Nat.add_mul _ _ _).symm

/-- This inequality bounds the loss after a finite sequence of trials. -/
theorem loss_pow_le (loss : ENNReal) (bounded : loss ≤ 1) (count : Nat) :
    1 - (1 - loss) ^ count ≤ count * loss := by
  have finite : loss ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top bounded
  have retainedBound : (1 : ENNReal) - loss ≤ 1 := tsub_le_self
  have powerBound : ((1 : ENNReal) - loss) ^ count ≤ 1 := pow_le_one₀ zero_le retainedBound
  apply (ENNReal.toReal_le_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) finite)).mp
  rw [ENNReal.toReal_sub_of_le powerBound ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le bounded ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have realBound : loss.toReal ≤ 1 := by
    simpa using (ENNReal.toReal_le_toReal finite ENNReal.one_ne_top).mpr bounded
  have bernoulli := one_add_mul_le_pow (a := -loss.toReal) (by linarith) count
  simpa only [sub_eq_add_neg, mul_neg] using (by linarith :
    1 - (1 + -loss.toReal) ^ count ≤ (count : ℝ) * loss.toReal)

/-- The failure probability grows at most linearly with the number of bounded draws. -/
theorem Code.cutoff_failure_linear {A : Type} {count : Nat} (attempts : Nat) (code : Code A count) :
    (code.cutoff attempts).law none ≤ count * (2 : ENNReal)⁻¹ ^ attempts :=
  (code.cutoff_failure attempts).trans
    (loss_pow_le _ (pow_le_one₀ zero_le (by norm_num)) count)

/-- The concrete offline sampler has a strict finite bit limit and a checked failure bound. -/
theorem offline_cutoff_failure :
    (offline.cutoff 256).law none ≤ 838208 / (2 : ENNReal) ^ 256 := by
  simpa only [ENNReal.inv_pow, div_eq_mul_inv, Nat.cast_ofNat] using offline.cutoff_failure_linear 256

end SimulatorSampling
end Kriterion.ArgoMAC.Security
