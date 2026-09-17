import Proof.Privacy.Source.FullSourceFlags
import Proof.Privacy.Source.Invalid.CompleteInvalidMaskComparison

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- This coin keeps the exact reconstructed tape and selected prefix. -/
def retainedPrefixCoin [FieldCertificate] [GroupCertificate] {State : Type}
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) :
    FullGatePrefixCoin State :=
  ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected)

/-- This weight keeps the actual good ghost event and its continuation. -/
def retainedGhostWeight [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden : BaseField) : ℝ≥0∞ :=
  if fullGateGhostBad ((retainedPrefixCoin retained full selected, output), hidden) then 0 else
    fullGatePrefixKernel scalar (fun table selected view rest => observe table selected view rest.2)
      fallback (retainedPrefixCoin retained full selected) output

/-- This weight keeps the actual good prescription and the missing hidden hash query. -/
def retainedMissWeight [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) : ℝ≥0∞ :=
  if fullGatePrefixBad (retainedPrefixCoin retained full selected) ∨
      retained.2.2.1.1 ∈ transcriptHashInputs (output.2.2.1 ++ output.2.2.2.2.2) then 0 else
    fullGatePrefixKernel scalar (fun table selected view rest => observe table selected view rest.2)
      fallback (retainedPrefixCoin retained full selected) output

/-- The exact curve change sends each good ghost weight to a missing-query weight. -/
theorem retainedGhostWeight_curveTransport [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden : BaseField) (mask : NonZeroBase)
    (invalid : ¬ OnCurve selected.1)
    (resultEq : retained.2.2.1.1 + retained.2.2.1.2.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) =
      hidden + mask.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)) :
    retainedGhostWeight scalar observe fallback retained full selected output hidden ≤
      retainedMissWeight scalar observe fallback (retainedKeyMask retained hidden mask)
        (fullCurveMaskEquiv retained.2.2.1.2.value mask.value selected.1 full) selected output := by
  by_cases bad : fullGateGhostBad ((retainedPrefixCoin retained full selected, output), hidden)
  · simp only [retainedGhostWeight, if_pos bad, zero_le]
  · have good : ¬ fullGatePrefixBad (retainedPrefixCoin retained full selected) :=
      fun member => bad (Or.inl member)
    have miss : hidden ∉ transcriptHashInputs (output.2.2.1 ++ output.2.2.2.2.2) :=
      fun member => bad (Or.inr (Or.inr member))
    have complete : FullSourceComplete full.1 := by
      rw [retainedPrefixCoin, fullGatePrefixBad_reconstructed] at good
      exact not_not.mp (not_or.mp good).1
    have changedGood := fullGatePrefixGood_curveTransport retained full selected hidden mask
      (retainedSourceRows scalar retained) invalid resultEq good
    have same := fullGatePrefixKernel_curveTransport scalar observe fallback retained full selected
      hidden mask complete resultEq
    simp only [retainedGhostWeight, if_neg bad, retainedMissWeight]
    have changedFlag : ¬ (fullGatePrefixBad
        (retainedPrefixCoin (retainedKeyMask retained hidden mask)
          (fullCurveMaskEquiv retained.2.2.1.2.value mask.value selected.1 full) selected) ∨
        (retainedKeyMask retained hidden mask).2.2.1.1 ∈
          transcriptHashInputs (output.2.2.1 ++ output.2.2.2.2.2)) :=
      not_or.mpr ⟨changedGood, miss⟩
    rw [if_neg changedFlag]
    exact (congrArg (fun distribution : PMF (FullGateTranscript State) => distribution output) same).symm.le


/-- This field-mask weight excludes only the zero mask. -/
def retainedFieldMissWeight [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden mask : BaseField)
    (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) : ℝ≥0∞ :=
  if nonzero : mask ≠ 0 then
    retainedMissWeight scalar observe fallback (retainedKeyMask retained hidden ⟨mask, nonzero⟩)
      full selected output else 0

/-- The old good ghost event excludes the zero new mask. -/
theorem retainedGhostWeight_offCurve [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden : BaseField) (invalid : ¬ OnCurve selected.1) :
    let mask := (offCurveOldKeyEquiv retained.2.2.1.2.value hidden selected.1 invalid).symm retained.2.2.1.1
    retainedGhostWeight scalar observe fallback retained full selected output hidden ≤
      nonzeroCompleteWeight (retainedFieldMissWeight scalar observe fallback retained selected output)
        hidden mask (fullCurveMaskEquiv retained.2.2.1.2.value mask selected.1 full) := by
  dsimp only
  set mask := (offCurveOldKeyEquiv retained.2.2.1.2.value hidden selected.1 invalid).symm retained.2.2.1.1
  have resultEq : retained.2.2.1.1 + retained.2.2.1.2.value *
      (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) =
      hidden + mask * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) := by
    dsimp only [mask, offCurveOldKeyEquiv, Equiv.coe_fn_symm_mk]
    rw [div_mul_cancel₀ _ (curveResidual_ne_zero selected.1 invalid)]
    ring
  by_cases zero : mask = 0
  · have diagonal : hidden = fullGateGhostResult (retainedPrefixCoin retained full selected) := by
      rw [retainedPrefixCoin, fullGateGhostResult_reconstructed]
      simpa only [zero, zero_mul, add_zero] using resultEq.symm
    have bad : fullGateGhostBad ((retainedPrefixCoin retained full selected, output), hidden) :=
      Or.inr (Or.inl diagonal)
    simp only [retainedGhostWeight, if_pos bad, zero_le]
  · have bound := retainedGhostWeight_curveTransport scalar observe fallback retained full selected
      output hidden ⟨mask, zero⟩ invalid resultEq
    simpa only [nonzeroCompleteWeight, if_neg zero, retainedFieldMissWeight, dif_pos zero] using bound


/-- The field-mask weight replaces both old key fields. -/
theorem retainedFieldMissWeight_rekey [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (key : BaseField) (mask : NonZeroBase) :
    retainedFieldMissWeight scalar observe fallback (retainedKeyMask retained key mask) selected output =
      retainedFieldMissWeight scalar observe fallback retained selected output := rfl

end
end Kriterion.ArgoMAC.Security
