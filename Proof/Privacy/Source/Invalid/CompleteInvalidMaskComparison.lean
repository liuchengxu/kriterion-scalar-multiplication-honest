import Proof.Privacy.Source.Invalid.CompleteInvalidSourceSum
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- The zero-mask guard acts on the whole retained source weight. -/
def nonzeroCompleteWeight
    (weight : BaseField → BaseField → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞)
    (key mask : BaseField) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) : ℝ≥0∞ :=
  if mask = 0 then 0 else weight key mask full

/-- The normalized source comparison pays no additive mask loss. -/
theorem fullCurveMaskEquiv_nonzero_sum_ge [FieldCertificate] [Fintype BaseField]
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (invalid : ¬ OnCurve input)
    (choose : Pipeline.Table → ℝ≥0∞)
    (weight : BaseField → BaseField → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞) :
    (∑' oldMask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) oldMask *
      ∑' hiddenKey, (PMF.uniformOfFintype BaseField) hiddenKey *
        ∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
          ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
            if FullSourceComplete full.1 then
              choose (circuitMaskSourceTable oldKey oldMask.value rows (decodeFullSource full)) *
                nonzeroCompleteWeight weight hiddenKey
                  ((offCurveOldKeyEquiv oldMask.value hiddenKey input invalid).symm oldKey)
                  (fullCurveMaskEquiv oldMask.value
                    ((offCurveOldKeyEquiv oldMask.value hiddenKey input invalid).symm oldKey) input full) else 0) ≤
    ∑' hiddenKey, (PMF.uniformOfFintype BaseField) hiddenKey *
      ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          if FullSourceComplete full.1 then
            choose (circuitMaskSourceTable hiddenKey mask.value rows (decodeFullSource full)) *
              weight hiddenKey mask.value full else 0 := by
  apply (fullCurveMaskEquiv_normalized_sum rows input invalid choose
    (nonzeroCompleteWeight weight)).le.trans
  simp only [nonzeroCompleteWeight]
  apply ENNReal.tsum_le_tsum
  intro hiddenKey
  apply mul_le_mul_right
  let sourceWeight := fun mask : BaseField =>
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      if FullSourceComplete full.1 then
        choose (circuitMaskSourceTable hiddenKey mask rows (decodeFullSource full)) * weight hiddenKey mask full else 0
  have each (mask : BaseField) :
      (∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        if FullSourceComplete full.1 then
          choose (circuitMaskSourceTable hiddenKey mask rows (decodeFullSource full)) *
            (if mask = 0 then 0 else weight hiddenKey mask full) else 0) =
      if mask = 0 then 0 else sourceWeight mask := by
    by_cases zero : mask = 0
    · simp only [if_pos zero, mul_zero, ite_self, tsum_zero]
    · simp only [if_neg zero, sourceWeight]
  simp_rw [each]
  exact nonzeroMask_weighted_mass_ge sourceWeight

end
end Kriterion.ArgoMAC.Security
