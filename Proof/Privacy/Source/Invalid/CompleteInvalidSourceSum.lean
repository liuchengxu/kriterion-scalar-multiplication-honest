import Proof.Privacy.Source.CompleteCurveTransport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- This inverse changes the old bridge key to the new mask. -/
def offCurveOldKeyEquiv [FieldCertificate] (oldMask hiddenKey : BaseField)
    (input : AffineInput) (invalid : ¬ OnCurve input) : BaseField ≃ BaseField where
  toFun mask := hiddenKey + (mask - oldMask) * (input.x ^ 3 + 3 - input.y ^ 2)
  invFun key := (key + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) - hiddenKey) /
    (input.x ^ 3 + 3 - input.y ^ 2)
  left_inv mask := by
    field_simp [curveResidual_ne_zero input invalid]
    ring
  right_inv key := by
    field_simp [curveResidual_ne_zero input invalid]
    ring

/-- The complete-source sum keeps the selected result while it moves the mask. -/
theorem fullCurveMaskEquiv_offCurve_weighted [FieldCertificate]
    (oldKey oldMask hiddenKey : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (invalid : ¬ OnCurve input)
    (choose : Pipeline.Table → ℝ≥0∞)
    (weight : ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    let mask := (offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey
    (∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable oldKey oldMask rows (decodeFullSource full)) *
          weight (fullCurveMaskEquiv oldMask mask input full) else 0) =
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable hiddenKey mask rows (decodeFullSource full)) * weight full else 0 := by
  dsimp only
  apply fullCurveMaskEquiv_weighted
  change oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) =
    hiddenKey + ((oldKey + oldMask * (input.x ^ 3 + 3 - input.y ^ 2) - hiddenKey) /
      (input.x ^ 3 + 3 - input.y ^ 2)) * (input.x ^ 3 + 3 - input.y ^ 2)
  rw [div_mul_cancel₀ _ (curveResidual_ne_zero input invalid)]
  ring

/-- One uniform old key gives one uniform new mask for the whole source weight. -/
theorem fullCurveMaskEquiv_key_sum [FieldCertificate] [Fintype BaseField]
    (oldMask hiddenKey : BaseField) (rows : FieldMacToECMac.Rows)
    (input : AffineInput) (invalid : ¬ OnCurve input)
    (choose : Pipeline.Table → ℝ≥0∞)
    (weight : BaseField → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    (∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        if FullSourceComplete full.1 then
          choose (circuitMaskSourceTable oldKey oldMask rows (decodeFullSource full)) *
            weight ((offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey)
              (fullCurveMaskEquiv oldMask
                ((offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey) input full) else 0) =
    ∑' mask, (PMF.uniformOfFintype BaseField) mask *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        if FullSourceComplete full.1 then
          choose (circuitMaskSourceTable hiddenKey mask rows (decodeFullSource full)) * weight mask full else 0 := by
  have each (oldKey : BaseField) := fullCurveMaskEquiv_offCurve_weighted oldKey oldMask hiddenKey
    rows input invalid choose (weight ((offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey))
  simp only at each
  simp_rw [each]
  have reindex := (offCurveOldKeyEquiv oldMask hiddenKey input invalid).tsum_eq
    (fun oldKey => (PMF.uniformOfFintype BaseField) oldKey *
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        if FullSourceComplete full.1 then
          choose (circuitMaskSourceTable hiddenKey
            ((offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey) rows (decodeFullSource full)) *
            weight ((offCurveOldKeyEquiv oldMask hiddenKey input invalid).symm oldKey) full else 0)
  simpa only [PMF.uniformOfFintype_apply, Equiv.symm_apply_apply] using reindex.symm

/-- The old nonzero mask has total mass one after the exact source reindex. -/
theorem fullCurveMaskEquiv_normalized_sum [FieldCertificate] [Fintype BaseField]
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (invalid : ¬ OnCurve input)
    (choose : Pipeline.Table → ℝ≥0∞)
    (weight : BaseField → BaseField → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    (∑' oldMask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) oldMask *
      ∑' hiddenKey, (PMF.uniformOfFintype BaseField) hiddenKey *
        ∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
          ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
            if FullSourceComplete full.1 then
              choose (circuitMaskSourceTable oldKey oldMask.value rows (decodeFullSource full)) *
                weight hiddenKey ((offCurveOldKeyEquiv oldMask.value hiddenKey input invalid).symm oldKey)
                  (fullCurveMaskEquiv oldMask.value
                    ((offCurveOldKeyEquiv oldMask.value hiddenKey input invalid).symm oldKey) input full) else 0) =
    ∑' hiddenKey, (PMF.uniformOfFintype BaseField) hiddenKey *
      ∑' mask, (PMF.uniformOfFintype BaseField) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          if FullSourceComplete full.1 then
            choose (circuitMaskSourceTable hiddenKey mask rows (decodeFullSource full)) * weight hiddenKey mask full else 0 := by
  simp_rw [fullCurveMaskEquiv_key_sum]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]


end
end Kriterion.ArgoMAC.Security
