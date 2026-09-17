import Proof.Privacy.Source.RetainedSourceTransport
import Proof.Privacy.Distribution.AdaptiveOffCurveDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 FieldMacToECMac
noncomputable section
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- This kernel keeps the actual source only when the selected input is invalid. -/
def invalidRetainedSource [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation)
    (selected : AffineInput × Aux) (key mask : BaseField) : PMF (Option Observation) := by
  classical
  exact if OnCurve selected.1 then PMF.pure none else
    (observe selected key mask (circuitMaskSampleSplit key mask rows selected.1 sample).2).map some

/-- This inverse recovers the original mask from the hidden key and independent curve result. -/
def invalidReindexedSource [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation)
    (selected : AffineInput × Aux) (key result : BaseField) : PMF (Option Observation) :=
  invalidRetainedSource sample rows observe selected key
    ((result - key) / (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))

/-- The inverse preserves all source fields on the invalid branch. -/
theorem invalidReindexedSource_actual [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation)
    (selected : AffineInput × Aux) (key mask : BaseField) :
    invalidReindexedSource sample rows observe selected key
      (key + mask * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)) =
    invalidRetainedSource sample rows observe selected key mask := by
  classical
  by_cases valid : OnCurve selected.1
  · simp only [invalidReindexedSource, invalidRetainedSource, if_pos valid]
  · unfold invalidReindexedSource
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ (curveResidual_ne_zero selected.1 valid)]

/-- A valid input contributes no mass to the invalid source event. -/
theorem invalidReindexedSource_selectedResult [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation)
    (selected : AffineInput × Aux) (pair : BaseField × BaseField) :
    invalidReindexedSource sample rows observe selected pair.1
      (selectedCurveIdealResult selected.1 pair) =
    invalidReindexedSource sample rows observe selected pair.1 pair.2 := by
  classical
  by_cases valid : OnCurve selected.1
  · simp only [invalidReindexedSource, invalidRetainedSource, if_pos valid]
  · simp only [selectedCurveIdealResult, if_neg valid]

/-- The full field mask makes the hidden key independent of the selected curve result. -/
theorem invalidRetainedSource_fullMask_eq [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (selected : PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation) :
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        invalidRetainedSource sample rows observe choice pair.1 pair.2) =
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        invalidReindexedSource sample rows observe choice pair.1 pair.2) := by
  have law := adaptiveCurveKey_uniform selected (invalidReindexedSource sample rows observe)
  simp only [invalidReindexedSource_actual, invalidReindexedSource_selectedResult] at law
  exact law

/-- The actual nonzero mask pays one field inverse for the complete invalid source observation. -/
theorem invalidRetainedSource_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (sample : PublicSample) (rows : Rows)
    (selected : PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → CircuitMaskSample → PMF Observation)
    (event : Set (Option Observation)) :
    |((selected.bind fun choice =>
        (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
          invalidReindexedSource sample rows observe choice pair.1 pair.2).toOuterMeasure event).toReal -
      ((selected.bind fun choice =>
        (PMF.uniformOfFintype BaseField).bind fun key =>
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            invalidRetainedSource sample rows observe choice key mask.value).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  have bound := adaptiveCurveMask_observation_bound selected
    (invalidReindexedSource sample rows observe) event
  simp only [invalidReindexedSource_actual, invalidReindexedSource_selectedResult] at bound
  exact bound

/-- Removing the zero mask gives a relative source bound for arbitrary nonnegative weights. -/
theorem nonzeroMask_weighted_mass_ge [FieldCertificate] [Fintype BaseField] (weight : BaseField → ℝ≥0∞) :
    (∑' mask, (PMF.uniformOfFintype BaseField) mask * if mask = 0 then 0 else weight mask) ≤
      ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask * weight mask.value := by
  classical
  have restricted := tsum_subtype {mask : BaseField | mask ≠ 0}
    (fun mask => (PMF.uniformOfFintype BaseField) mask * weight mask)
  have restrictEq :
      (∑' mask, (PMF.uniformOfFintype BaseField) mask * if mask = 0 then 0 else weight mask) =
        ∑' mask : {mask : BaseField // mask ≠ 0}, (PMF.uniformOfFintype BaseField) mask.val * weight mask.val := by
    calc
      _ = ∑' mask : BaseField, ({value : BaseField | value ≠ 0}.indicator
        (fun value => (PMF.uniformOfFintype BaseField) value * weight value) mask) := by
          apply tsum_congr
          intro mask
          by_cases zero : mask = 0 <;> simp [Set.indicator, zero]
      _ = _ := restricted.symm
  rw [restrictEq, ← nonZeroBaseSubtypeEquiv.tsum_eq]
  apply ENNReal.tsum_le_tsum
  intro mask
  simp only [PMF.uniformOfFintype_apply]
  apply mul_le_mul_left
  apply ENNReal.inv_le_inv.mpr
  exact_mod_cast Fintype.card_le_of_injective NonZeroBase.value
    (fun first second equal => by cases first; cases second; simp_all)

private theorem uniform_product_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (weight : A → B → ℝ≥0∞) :
    (∑' pair : A × B, (PMF.uniformOfFintype (A × B)) pair * weight pair.1 pair.2) =
      ∑' first, (PMF.uniformOfFintype A) first *
        ∑' second, (PMF.uniformOfFintype B) second * weight first second := by
  rw [ENNReal.tsum_prod']
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [← ENNReal.tsum_mul_left, mul_assoc]

/-- The invalid source has a relative bound after removal of the hidden-key diagonal. -/
theorem offCurve_nonzero_weighted_mass_ge [FieldCertificate] [Fintype BaseField]
    (input : AffineInput) (invalid : ¬ OnCurve input) (weight : BaseField → BaseField → ℝ≥0∞) :
    (∑' pair : BaseField × BaseField, (PMF.uniformOfFintype (BaseField × BaseField)) pair *
      if pair.1 = pair.2 then 0 else
        weight pair.1 ((pair.2 - pair.1) / (input.x ^ 3 + 3 - input.y ^ 2))) ≤
      ∑' key, (PMF.uniformOfFintype BaseField) key *
        ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask * weight key mask.value := by
  classical
  have nonzero := curveResidual_ne_zero input invalid
  have reindex := (offCurveKeyEquiv _ nonzero).tsum_eq
    (fun pair : BaseField × BaseField => (PMF.uniformOfFintype (BaseField × BaseField)) pair *
      if pair.1 = pair.2 then 0 else
        weight pair.1 ((pair.2 - pair.1) / (input.x ^ 3 + 3 - input.y ^ 2)))
  have pointwise (pair : BaseField × BaseField) :
      (if (offCurveKeyEquiv _ nonzero pair).1 = (offCurveKeyEquiv _ nonzero pair).2 then 0 else
        weight (offCurveKeyEquiv _ nonzero pair).1
          (((offCurveKeyEquiv _ nonzero pair).2 - (offCurveKeyEquiv _ nonzero pair).1) /
            (input.x ^ 3 + 3 - input.y ^ 2))) =
      if pair.2 = 0 then 0 else weight pair.1 pair.2 := by
    simp only [offCurveKeyEquiv, Equiv.coe_fn_mk, add_sub_cancel_left,
      mul_div_cancel_right₀ _ nonzero]
    have equal : pair.1 = pair.1 + pair.2 * (input.x ^ 3 + 3 - input.y ^ 2) ↔ pair.2 = 0 := by
      rw [eq_comm, add_eq_left, mul_eq_zero]
      simp only [nonzero, or_false]
    simp only [equal]
  simp only [PMF.uniformOfFintype_apply, pointwise] at reindex
  simp only [PMF.uniformOfFintype_apply]
  rw [← reindex]
  have product := uniform_product_weight (fun key mask : BaseField => if mask = 0 then 0 else weight key mask)
  simp only [PMF.uniformOfFintype_apply] at product
  rw [product]
  apply ENNReal.tsum_le_tsum
  intro key
  simpa only [PMF.uniformOfFintype_apply] using
    mul_le_mul_right (nonzeroMask_weighted_mass_ge (weight key)) ((Fintype.card BaseField : ℝ≥0∞)⁻¹)

end
end Kriterion.ArgoMAC.Security
