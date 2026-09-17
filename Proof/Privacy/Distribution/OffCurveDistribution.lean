import Proof.Privacy.Distribution.CurveDistribution
import Proof.Privacy.Distribution.HashDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- A nonzero curve residual separates the bridge key from the selected result. -/
def offCurveKeyEquiv [FieldCertificate] (residual : BaseField) (nonzero : residual ≠ 0) :
    (BaseField × BaseField) ≃ (BaseField × BaseField) where
  toFun pair := (pair.1, pair.1 + pair.2 * residual)
  invFun pair := (pair.1, (pair.2 - pair.1) / residual)
  left_inv pair := by
    apply Prod.ext
    · rfl
    · dsimp
      rw [add_sub_cancel_left, mul_div_cancel_right₀ _ nonzero]
  right_inv pair := by
    apply Prod.ext
    · rfl
    · dsimp
      rw [div_mul_cancel₀ _ nonzero]
      ring

/-- An off-curve input has a nonzero residual. -/
theorem curveResidual_ne_zero (input : AffineInput) (offCurve : ¬ OnCurve input) :
    input.x ^ 3 + 3 - input.y ^ 2 ≠ 0 := by
  intro zero
  apply offCurve
  exact (sub_eq_zero.mp zero).symm

/-- Uniform bridge keys and masks give independent uniform keys and results. -/
theorem map_uniform_offCurveKey [FieldCertificate] (input : AffineInput)
    (offCurve : ¬ OnCurve input) :
    (PMF.uniformOfFintype (BaseField × BaseField)).map
        (fun pair => (pair.1, pair.1 + pair.2 * (input.x ^ 3 + 3 - input.y ^ 2))) =
      PMF.uniformOfFintype (BaseField × BaseField) :=
  map_uniformOfFintype_equivBetween
    (offCurveKeyEquiv _ (curveResidual_ne_zero input offCurve))

/-- The result and the free curve masks determine one complete mask view. -/
def curveAssembleEquiv (input : AffineInput) :
    (BaseField × CurveMaskData) ≃ CurveMaskView :=
  (Equiv.sigmaEquivProd BaseField CurveMaskData).symm.trans
    ((Equiv.sigmaCongrRight (curveMaskFiberEquiv input)).trans
      (Equiv.sigmaFiberEquiv (curveMaskResult input)))

/-- This change of variables keeps the hidden bridge key in the complete off-curve view. -/
def offCurvePublicEquiv [FieldCertificate] (input : AffineInput)
    (offCurve : ¬ OnCurve input) :
    ((BaseField × BaseField) × CurveMaskData) ≃ (BaseField × CurveMaskView) :=
  (Equiv.prodCongrRight (fun pair : BaseField × BaseField =>
    curveMaskShiftEquiv pair.2 input)).trans
      ((Equiv.prodCongr (offCurveKeyEquiv _ (curveResidual_ne_zero input offCurve))
        (Equiv.refl CurveMaskData)).trans
          ((Equiv.prodAssoc BaseField BaseField CurveMaskData).trans
            (Equiv.prodCongr (Equiv.refl BaseField) (curveAssembleEquiv input))))

/-- The equivalence uses the concrete curve-mask map. -/
theorem offCurvePublicEquiv_apply [FieldCertificate] (input : AffineInput)
    (offCurve : ¬ OnCurve input) (source : (BaseField × BaseField) × CurveMaskData) :
    offCurvePublicEquiv input offCurve source =
      (source.1.1, (curveMaskViewEquiv source.1.1 source.1.2 input source.2).1) := rfl

/-- The full off-curve view leaves the bridge key independent and uniform. -/
theorem map_uniform_offCurvePublic [FieldCertificate] (input : AffineInput)
    (offCurve : ¬ OnCurve input) :
    (PMF.uniformOfFintype ((BaseField × BaseField) × CurveMaskData)).map
        (fun source =>
          (source.1.1, (curveMaskViewEquiv source.1.1 source.1.2 input source.2).1)) =
      PMF.uniformOfFintype (BaseField × CurveMaskView) :=
  map_uniformOfFintype_equivBetween (offCurvePublicEquiv input offCurve)

/-- This equivalence identifies the nonzero field representation with its subtype. -/
def nonZeroBaseSubtypeEquiv : NonZeroBase ≃ {value : BaseField // value ≠ 0} where
  toFun value := ⟨value.value, value.nonzero⟩
  invFun value := ⟨value.1, value.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The nonzero mask domain omits one field element. -/
theorem card_nonZeroBase : Fintype.card NonZeroBase = baseFieldModulus - 1 := by
  rw [Fintype.card_congr nonZeroBaseSubtypeEquiv]
  have card {α : Type} [Fintype α] (zero : α) [Fintype {x : α // x ≠ zero}] :
      Fintype.card {x : α // x ≠ zero} = Fintype.card α - 1 := by
    classical
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact (card (0 : BaseField)).trans (congrArg (fun count => count - 1) (ZMod.card _))

/-- Replacing a nonzero curve mask by a full field mask costs at most one field inverse. -/
theorem curveMask_observation_bound [FieldCertificate] {Observation : Type*}
    (observe : BaseField → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype BaseField).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype NonZeroBase).bind
        (fun mask => observe mask.value)).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  have bound := uniformEmbedding_observation_bound NonZeroBase.value
    (fun first second equal => by cases first; cases second; simp_all) observe event
  rw [card_nonZeroBase, show Fintype.card BaseField = baseFieldModulus from ZMod.card _] at bound
  have positive : 1 ≤ baseFieldModulus := by decide
  rw [Nat.cast_sub positive, Nat.cast_one] at bound
  have denominator : (baseFieldModulus : ℝ) ≠ 0 := by exact_mod_cast (by decide : baseFieldModulus ≠ 0)
  convert bound using 1
  · rfl
  · field_simp
    ring

end

end Kriterion.ArgoMAC.Security
