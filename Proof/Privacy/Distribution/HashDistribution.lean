import Proof.Privacy.Distribution.PublicDistribution
import Proof.Shared.HCoefficient

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- A finite subset replacement bounds every later randomized observation. -/
theorem uniformEmbedding_observation_bound
    {A B Observation : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (embed : A → B) (injective : Function.Injective embed)
    (observe : B → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype B).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype A).bind (observe ∘ embed)).toOuterMeasure event).toReal| ≤
      1 - (Fintype.card A : ℝ) / Fintype.card B := by
  classical
  have density (output : Observation) :
      ((Fintype.card A : ENNReal) / Fintype.card B) *
        ((PMF.uniformOfFintype A).bind (observe ∘ embed)) output ≤
          ((PMF.uniformOfFintype B).bind observe) output := by
    have cancel : ((Fintype.card A : ENNReal) / Fintype.card B) *
        (Fintype.card A : ENNReal)⁻¹ = (Fintype.card B : ENNReal)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm,
        ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
          (ENNReal.natCast_ne_top _), one_mul]
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Function.comp_apply,
      ← ENNReal.tsum_mul_left, ← mul_assoc, cancel]
    exact ENNReal.summable.tsum_le_tsum_of_inj embed injective
      (fun _ _ => bot_le) (fun _ => le_rfl) ENNReal.summable
  have ratio_le : (Fintype.card A : ℝ) / Fintype.card B ≤ 1 := by
    apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
    exact_mod_cast Fintype.card_le_of_injective embed injective
  have bound := hCoefficient_event
    ((PMF.uniformOfFintype B).bind observe)
    ((PMF.uniformOfFintype A).bind (observe ∘ embed)) ∅ event 0
    (1 - (Fintype.card A : ℝ) / Fintype.card B) (sub_nonneg.mpr ratio_le)
    (by simp) (fun output _ => by
      have h := ENNReal.toReal_mono
        (((PMF.uniformOfFintype B).bind observe).apply_ne_top output) (density output)
      simpa only [sub_sub_cancel, ENNReal.toReal_mul, ENNReal.toReal_div,
        ENNReal.toReal_natCast] using h)
  simpa only [zero_add] using bound

/-- The whole product tape incurs at most the sum of its coordinate losses. -/
theorem uniformEmbedding_family_observation_bound
    {Index A B Observation : Type*} [Fintype Index] [DecidableEq Index] [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (embed : A → B) (injective : Function.Injective embed)
    (observe : (Index → B) → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype (Index → B)).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype (Index → A)).bind
        (fun tape => observe (fun index => embed (tape index)))).toOuterMeasure event).toReal| ≤
      Fintype.card Index * (1 - (Fintype.card A : ℝ) / Fintype.card B) := by
  classical
  have bound := uniformEmbedding_observation_bound
    (fun tape : Index → A => fun index => embed (tape index))
    (fun first second same => funext fun index => injective (congrFun same index)) observe event
  simp only [Fintype.card_fun, Nat.cast_pow, ← div_pow] at bound
  apply bound.trans
  have bernoulli := one_add_mul_sub_le_pow
    (show (-1 : ℝ) ≤ (Fintype.card A : ℝ) / Fintype.card B from
      (by norm_num : (-1 : ℝ) ≤ 0).trans (by positivity))
    (Fintype.card Index)
  linarith

/-- This source embeds uniform field residues and quotients into the full hash domain. -/
def goodHashLiftSource (sample : BaseField × HashLiftQuotient) : FullHashLift :=
  hashLiftSplitEquiv.symm (Sum.inl (goodHashLiftEquiv.symm sample))

set_option exponentiation.threshold 400 in
/-- The source uses the simulator's actual good hash lift. -/
theorem goodHashLiftSource_eq (sample : BaseField × HashLiftQuotient) :
    goodHashLiftSource sample = (goodHashLift sample.1 sample.2).1.toFin := by
  apply Fin.ext
  change (goodHashLiftSource sample).val = (goodHashLift sample.1 sample.2).1.toNat
  rw [goodHashLift_toNat]
  rfl

set_option exponentiation.threshold 400 in
/-- Whole-tape rounding bounds every later randomized or adaptive observation. -/
theorem hashLift_family_observation_bound
    {Index Observation : Type*} [Fintype Index] [DecidableEq Index]
    (observe : (Index → FullHashLift) → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype (Index → FullHashLift)).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype (Index → BaseField × HashLiftQuotient)).bind
        (fun tape => observe (fun index => goodHashLiftSource (tape index)))).toOuterMeasure
          event).toReal| ≤
      (Fintype.card Index : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  have bound := uniformEmbedding_family_observation_bound goodHashLiftSource
    (hashLiftSplitEquiv.symm.injective.comp
      (Sum.inl_injective.comp goodHashLiftEquiv.symm.injective)) observe event
  have cardGood : Fintype.card (BaseField × HashLiftQuotient) =
      hashLiftQuotientCount * baseFieldModulus := by
    exact (Fintype.card_congr goodHashLiftEquiv.symm).trans (Fintype.card_fin _)
  rw [cardGood, show Fintype.card FullHashLift = 2 ^ 384 from Fintype.card_fin _] at bound
  have fibers : ((hashLiftQuotientCount * baseFieldModulus : ℕ) : ℝ) +
      ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) = (2 : ℝ) ^ 384 := by
    exact_mod_cast hashLiftFiberCount
  have gap : 1 - ((hashLiftQuotientCount * baseFieldModulus : ℕ) : ℝ) / (2 : ℝ) ^ 384 =
      ((2 ^ 384 % baseFieldModulus : ℕ) : ℝ) / 2 ^ 384 := by
    apply (eq_div_iff (by positivity : (2 : ℝ) ^ 384 ≠ 0)).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  simpa only [Nat.cast_pow, Nat.cast_ofNat, gap, mul_div_assoc] using bound


/-- Hash rounding retains an independent finite source in every later observation. -/
theorem hashLift_family_product_observation_bound
    {Index Rest Observation : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Rest] [Nonempty Rest]
    (observe : ((Index → FullHashLift) × Rest) → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype ((Index → FullHashLift) × Rest)).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype ((Index → BaseField × HashLiftQuotient) × Rest)).bind
        (fun pair => observe ((fun index => goodHashLiftSource (pair.1 index)), pair.2))).toOuterMeasure
          event).toReal| ≤
      (Fintype.card Index : ℝ) * (2 ^ 384 % baseFieldModulus : ℕ) / 2 ^ 384 := by
  rw [uniform_product_bind, uniform_product_bind]
  exact hashLift_family_observation_bound
    (fun hash => (PMF.uniformOfFintype Rest).bind fun rest => observe (hash, rest)) event

end

end Kriterion.ArgoMAC.Security
