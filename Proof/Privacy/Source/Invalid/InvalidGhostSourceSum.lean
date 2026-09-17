import Proof.Privacy.Source.Invalid.InvalidGhostSourceTransport
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

private theorem normalized_ghost_weight_le [FieldCertificate]
    (rows : FieldMacToECMac.Rows) (input : AffineInput) (invalid : ¬ OnCurve input)
    (choose : Pipeline.Table → ℝ≥0∞)
    (oldWeight : NonZeroBase → BaseField → BaseField →
      ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞)
    (weight : BaseField → BaseField → ((RawCircuitGate → FullHashLift) × CircuitHashRest) → ℝ≥0∞)
    (bound : ∀ oldMask hidden oldKey full,
      oldWeight oldMask hidden oldKey full ≤
        nonzeroCompleteWeight weight hidden ((offCurveOldKeyEquiv oldMask.value hidden input invalid).symm oldKey)
          (fullCurveMaskEquiv oldMask.value
            ((offCurveOldKeyEquiv oldMask.value hidden input invalid).symm oldKey) input full)) :
    (∑' oldMask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) oldMask *
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        ∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
          ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
            if FullSourceComplete full.1 then
              choose (circuitMaskSourceTable oldKey oldMask.value rows (decodeFullSource full)) *
                oldWeight oldMask hidden oldKey full else 0) ≤
    ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
      ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          if FullSourceComplete full.1 then
            choose (circuitMaskSourceTable hidden mask.value rows (decodeFullSource full)) *
              weight hidden mask.value full else 0 := by
  apply le_trans ?_ (fullCurveMaskEquiv_nonzero_sum_ge rows input invalid choose weight)
  apply ENNReal.tsum_le_tsum
  intro oldMask
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro hidden
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro oldKey
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro full
  apply mul_le_mul_right
  by_cases complete : FullSourceComplete full.1
  · rw [if_pos complete, if_pos complete]
    exact mul_le_mul_right (bound oldMask hidden oldKey full) _
  · rw [if_neg complete, if_neg complete]

/-- This source weight keeps the three independent key and mask samples. -/
def retainedOldGhostWeight [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (oldMask : NonZeroBase) (hidden oldKey : BaseField)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) : ℝ≥0∞ :=
  retainedGhostWeight scalar observe fallback (retainedKeyMask retained oldKey oldMask)
    full selected output hidden

private theorem fieldMiss_nonzero [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden : BaseField) (mask : NonZeroBase)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :
    retainedFieldMissWeight scalar observe fallback retained selected output hidden mask.value full =
      retainedMissWeight scalar observe fallback (retainedKeyMask retained hidden mask) full selected output := by
  simp only [retainedFieldMissWeight, dif_pos mask.nonzero]

set_option maxRecDepth 2048 in
/-- The normalized invalid ghost sum is bounded by the actual missing-query source sum. -/
theorem retainedGhostWeight_normalized_sum_le [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (invalid : ¬ OnCurve selected.1)
    (choose : Pipeline.Table → ℝ≥0∞) :
    (∑' oldMask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) oldMask *
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        ∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
          ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
            if FullSourceComplete full.1 then
              choose (circuitMaskSourceTable oldKey oldMask.value (retainedSourceRows scalar retained)
                (decodeFullSource full)) *
              retainedGhostWeight scalar observe fallback (retainedKeyMask retained oldKey oldMask)
                full selected output hidden else 0) ≤
    ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
      ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          if FullSourceComplete full.1 then
            choose (circuitMaskSourceTable hidden mask.value (retainedSourceRows scalar retained)
              (decodeFullSource full)) *
            retainedMissWeight scalar observe fallback (retainedKeyMask retained hidden mask)
              full selected output else 0 := by
  have bound (oldMask : NonZeroBase) (hidden oldKey : BaseField)
      (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) :=
    retainedGhostWeight_offCurve scalar observe fallback
      (retainedKeyMask retained oldKey oldMask) full selected output hidden invalid
  simp only [retainedFieldMissWeight_rekey] at bound
  have result := normalized_ghost_weight_le (retainedSourceRows scalar retained) selected.1 invalid choose
    (retainedOldGhostWeight scalar observe fallback retained selected output)
    (retainedFieldMissWeight scalar observe fallback retained selected output) bound
  simpa only [retainedOldGhostWeight, fieldMiss_nonzero] using result

end
end Kriterion.ArgoMAC.Security
