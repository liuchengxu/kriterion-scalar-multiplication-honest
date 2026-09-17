import Proof.Privacy.Source.Invalid.InvalidGhostSourceSum
import Proof.Privacy.Source.Invalid.InvalidGhostSourceSupport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- The complete-source guard removes no actual good ghost weight. -/
theorem retainedGhostWeight_selected_sum_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript adversary.State) (invalid : ¬ OnCurve output.2.1.1)
    (choose : Pipeline.Table → ℝ≥0∞) :
    (∑' oldMask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) oldMask *
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        ∑' oldKey, (PMF.uniformOfFintype BaseField) oldKey *
          ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
            (choose (circuitMaskSourceTable oldKey oldMask.value (retainedSourceRows scalar retained)
              (decodeFullSource full)) *
              retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
                (retainedKeyMask retained oldKey oldMask) full selected output hidden)) ≤
    ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
      ∑' mask : NonZeroBase, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          (choose (circuitMaskSourceTable hidden mask.value (retainedSourceRows scalar retained)
            (decodeFullSource full)) *
            retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              (retainedKeyMask retained hidden mask) full selected output) := by
  by_cases selectedInvalid : ¬ OnCurve selected.1
  · have bound := retainedGhostWeight_normalized_sum_le scalar
      (gateSourceObserve adversary parameter auxiliary) fallback retained selected output selectedInvalid choose
    apply le_trans ?_ (bound.trans ?_)
    · apply ENNReal.tsum_le_tsum
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
      · rw [if_pos complete]
      · rw [if_neg complete, retainedGhostWeight_incomplete scalar _ fallback _ full selected output hidden complete,
          mul_zero]
    · apply ENNReal.tsum_le_tsum
      intro hidden
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro mask
      apply mul_le_mul_right
      apply ENNReal.tsum_le_tsum
      intro full
      apply mul_le_mul_right
      split_ifs <;> first | exact le_rfl | exact bot_le
  · have different : output.2.1.1 ≠ selected.1 := by
      intro same
      exact selectedInvalid (same ▸ invalid)
    have zero (oldKey : BaseField) (oldMask : NonZeroBase)
        (full : (RawCircuitGate → FullHashLift) × CircuitHashRest) (hidden : BaseField) :=
      retainedGhostWeight_different_input adversary parameter auxiliary scalar fallback
        (retainedKeyMask retained oldKey oldMask) full selected output hidden different
    simp only [zero, mul_zero, tsum_zero, zero_le]

end
end Kriterion.ArgoMAC.Security
