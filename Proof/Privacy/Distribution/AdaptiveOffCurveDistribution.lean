import Proof.Privacy.Distribution.OffCurveDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

attribute [local instance] Classical.propDecidable

/-- This split retains the true bridge key and replaces the off-curve result. -/
def selectedCurveKeyEquiv [FieldCertificate] (input : AffineInput) :
    (BaseField × BaseField) ≃ (BaseField × BaseField) :=
  if valid : OnCurve input then Equiv.refl _
  else offCurveKeyEquiv _ (curveResidual_ne_zero input valid)

/-- The valid branch returns the true key. The invalid branch returns a fresh field value. -/
def selectedCurveIdealResult (input : AffineInput) (pair : BaseField × BaseField) : BaseField :=
  if OnCurve input then pair.1 else pair.2

/-- The split gives the actual selected curve result in both branches. -/
theorem selectedCurveKeyEquiv_result [FieldCertificate]
    (input : AffineInput) (pair : BaseField × BaseField) :
    selectedCurveIdealResult input (selectedCurveKeyEquiv input pair) =
      pair.1 + pair.2 * (input.x ^ 3 + 3 - input.y ^ 2) := by
  by_cases valid : OnCurve input
  · have residual : input.x ^ 3 + 3 - input.y ^ 2 = 0 := sub_eq_zero.mpr valid.symm
    simp [selectedCurveIdealResult, selectedCurveKeyEquiv, valid, residual]
  · simp [selectedCurveIdealResult, selectedCurveKeyEquiv, valid, offCurveKeyEquiv]

/-- The split keeps the true key for the actual hash and EncPRF data. -/
theorem selectedCurveKeyEquiv_key [FieldCertificate]
    (input : AffineInput) (pair : BaseField × BaseField) :
    (selectedCurveKeyEquiv input pair).1 = pair.1 := by
  by_cases valid : OnCurve input <;>
    simp [selectedCurveKeyEquiv, valid, offCurveKeyEquiv]

/-- The full field mask gives the exact selected-result law after any independent input choice. -/
theorem adaptiveCurveKey_uniform [FieldCertificate] {Aux Observation : Type*}
    (selected : PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → PMF Observation) :
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        observe choice pair.1
          (pair.1 + pair.2 * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))) =
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        observe choice pair.1 (selectedCurveIdealResult choice.1 pair)) := by
  apply congrArg (selected.bind)
  funext choice
  have uniform := map_uniformOfFintype_equivBetween (selectedCurveKeyEquiv choice.1)
  conv_rhs => rw [← uniform, PMF.bind_map]
  simp only [Function.comp_def, selectedCurveKeyEquiv_key, selectedCurveKeyEquiv_result]

/-- The actual nonzero mask changes this complete adaptive observation by at most one field inverse. -/
theorem adaptiveCurveMask_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (selected : PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → PMF Observation)
    (event : Set Observation) :
    |((selected.bind fun choice =>
        (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
          observe choice pair.1 (selectedCurveIdealResult choice.1 pair)).toOuterMeasure event).toReal -
      ((selected.bind fun choice =>
        (PMF.uniformOfFintype BaseField).bind fun key =>
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            observe choice key
              (key + mask.value * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  rw [← adaptiveCurveKey_uniform]
  have product : ∀ choice : AffineInput × Aux,
      (PMF.uniformOfFintype (BaseField × BaseField)).bind
        (fun pair => observe choice pair.1
          (pair.1 + pair.2 * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))) =
      (PMF.uniformOfFintype BaseField).bind fun key =>
        (PMF.uniformOfFintype BaseField).bind fun mask =>
          observe choice key (key + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)) := by
    intro choice
    rw [uniform_prod_eq_bind, PMF.bind_bind]
    simp only [PMF.bind_map]
    rw [PMF.bind_comm]
    rfl
  simp only [product]
  have reorder {Mask : Type} (masks : PMF Mask) (value : Mask → BaseField) :
      (selected.bind fun choice => (PMF.uniformOfFintype BaseField).bind fun key =>
        masks.bind fun mask => observe choice key
          (key + value mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))) =
      (masks.bind fun mask => selected.bind fun choice =>
        (PMF.uniformOfFintype BaseField).bind fun key =>
          observe choice key (key + value mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))) := by
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) masks]
    exact PMF.bind_comm _ _ _
  have full := reorder (PMF.uniformOfFintype BaseField) id
  simp only [id_eq] at full
  rw [full, reorder (PMF.uniformOfFintype NonZeroBase) NonZeroBase.value]
  exact curveMask_observation_bound
    (fun mask => (selected.bind fun choice =>
      (PMF.uniformOfFintype BaseField).bind fun key =>
        observe choice key (key + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)))) event

end

end Kriterion.ArgoMAC.Security
