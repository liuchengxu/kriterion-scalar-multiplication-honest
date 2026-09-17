import Proof.Privacy.Simulator.IdealEncoding
import Proof.Privacy.Distribution.PointDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

instance nonZeroBaseFintype : Fintype NonZeroBase :=
  Fintype.ofInjective NonZeroBase.value (by
    intro first second equal
    cases first
    cases second
    simp_all)

instance nonZeroBaseNonempty [FieldCertificate] : Nonempty NonZeroBase :=
  ⟨⟨1, one_ne_zero⟩⟩

/-- This operation multiplies all homogeneous coordinates by one nonzero scale. -/
def scaleHomogeneous (scale : NonZeroBase) (value : FieldMacToECMac.HomogeneousValue) :
    FieldMacToECMac.HomogeneousValue :=
  ⟨scale.value * value.x, scale.value * value.y, scale.value * value.z⟩

/-- A nonzero factor permutes the nonzero scales. -/
def nonzeroScaleMulEquiv [FieldCertificate] (factor : NonZeroBase) :
    NonZeroBase ≃ NonZeroBase where
  toFun scale := ⟨scale.value * factor.value, mul_ne_zero scale.nonzero factor.nonzero⟩
  invFun scale := ⟨scale.value / factor.value, div_ne_zero scale.nonzero factor.nonzero⟩
  left_inv scale := by
    cases scale
    simp only [NonZeroBase.mk.injEq]
    exact mul_div_cancel_right₀ _ factor.nonzero
  right_inv scale := by
    cases scale
    simp only [NonZeroBase.mk.injEq]
    exact div_mul_cancel₀ _ factor.nonzero

/-- A decoded homogeneous value has a nonzero scale representative. -/
theorem exists_homogeneous_scale [FieldCertificate]
    (value : FieldMacToECMac.HomogeneousValue) (point : Point)
    (decoded : Garbling.decodeHomogeneous value = some point) :
    ∃ scale : NonZeroBase, value = homogeneousOfPoint point scale := by
  by_cases zZero : value.z = 0
  · rw [Garbling.decodeHomogeneous, if_pos zZero] at decoded
    split_ifs at decoded with valid
    · have equal : point = 0 := (Option.some.inj decoded).symm
      subst point
      refine ⟨⟨value.y, valid.2⟩, ?_⟩
      cases value
      simp_all [homogeneousOfPoint]
      exact valid.1
  · rw [Garbling.decodeHomogeneous, if_neg zZero, decodePoint] at decoded
    split_ifs at decoded with valid
    · refine ⟨⟨value.z, zZero⟩, ?_⟩
      rw [← Option.some.inj decoded]
      cases value
      simp_all [homogeneousOfPoint]

/-- Scaling a representative multiplies its nonzero scale. -/
theorem scaleHomogeneous_representative [FieldCertificate]
    (point : Point) (scale factor : NonZeroBase) :
    scaleHomogeneous scale (homogeneousOfPoint point factor) =
      homogeneousOfPoint point (nonzeroScaleMulEquiv factor scale) := by
  cases point <;>
    simp [scaleHomogeneous, homogeneousOfPoint, nonzeroScaleMulEquiv,
      mul_left_comm]

/-- Uniform scaling depends only on the decoded point. -/
theorem map_uniform_scaleHomogeneous [FieldCertificate]
    (value : FieldMacToECMac.HomogeneousValue) (point : Point)
    (decoded : Garbling.decodeHomogeneous value = some point) :
    (PMF.uniformOfFintype NonZeroBase).map (fun scale => scaleHomogeneous scale value) =
      (PMF.uniformOfFintype NonZeroBase).map (homogeneousOfPoint point) := by
  obtain ⟨factor, rfl⟩ := exists_homogeneous_scale value point decoded
  simp_rw [scaleHomogeneous_representative]
  change (PMF.uniformOfFintype NonZeroBase).map
    (homogeneousOfPoint point ∘ nonzeroScaleMulEquiv factor) = _
  rw [← PMF.map_comp, uniform_map_equiv]

end

end Kriterion.ArgoMAC.Security
