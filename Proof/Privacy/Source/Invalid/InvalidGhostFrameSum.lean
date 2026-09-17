import Proof.Privacy.Source.Invalid.InvalidGhostProductSum
import Proof.Privacy.Source.RetainedFrameDistribution
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
private theorem weightedEq {A : Type*} (samples : PMF A) {left right : A → ℝ≥0∞}
    (same : ∀ value, left value = right value) :
    (∑' value, samples value * left value) = ∑' value, samples value * right value := by
  exact tsum_congr fun value => congrArg (samples value * ·) (same value)

private theorem frameComparison [FieldCertificate] [GroupCertificate]
    [Fintype MaskRetainedTape] [Fintype RetainedSourceFrame] [Fintype BaseField]
    (oldWeight newWeight : MaskRetainedTape → ℝ≥0∞)
    (bound : ∀ frame : RetainedSourceFrame,
      (∑' key, (PMF.uniformOfFintype BaseField) key *
        ∑' mask, (PMF.uniformOfFintype NonZeroBase) mask *
          oldWeight (retainedFrameEquiv.symm (frame, key, mask))) ≤
      ∑' key, (PMF.uniformOfFintype BaseField) key *
        ∑' mask, (PMF.uniformOfFintype NonZeroBase) mask *
          newWeight (retainedFrameEquiv.symm (frame, key, mask))) :
    (∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained * oldWeight retained) ≤
    ∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained * newWeight retained := by
  rw [retainedFrame_weight_sum, retainedFrame_weight_sum]
  exact ENNReal.tsum_le_tsum fun frame => mul_le_mul_right (bound frame) _

variable [Nonempty BaseField] [Nonempty ((RawCircuitGate → FullHashLift) × CircuitHashRest)]

/-- This weight sums the actual ghost kernel over its full source and selected prefix. -/
def retainedGhostTotal [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (retained : MaskRetainedTape) : ℝ≥0∞ :=
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        ∑' selected, retainedPrefixChoice adversary parameter auxiliary retained selected
          (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) (decodeFullSource full)) *
          ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
            retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              retained full selected output hidden

/-- This weight sums the actual missing-query kernel over the same source. -/
def retainedMissTotal [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (retained : MaskRetainedTape) : ℝ≥0∞ :=
      ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
        ∑' selected, retainedPrefixChoice adversary parameter auxiliary retained selected
          (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
            (retainedSourceRows scalar retained) (decodeFullSource full)) *
          retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
            retained full selected output

private theorem ghostTotal_rekey [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (retained : MaskRetainedTape) (key : BaseField) (mask : NonZeroBase) :
    retainedGhostTotal adversary parameter auxiliary scalar fallback output
      (retainedKeyMask retained key mask) =
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
        ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
          retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden := by
  unfold retainedGhostTotal
  apply tsum_congr
  intro full
  apply congrArg (_ * ·)
  apply tsum_congr
  intro selected
  have choice : retainedPrefixChoice adversary parameter auxiliary
      (retainedKeyMask retained key mask) selected
      (circuitMaskSourceTable (retainedKeyMask retained key mask).2.2.1.1
        (retainedKeyMask retained key mask).2.2.1.2.value
        (retainedSourceRows scalar (retainedKeyMask retained key mask)) (decodeFullSource full)) =
      retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected := by
    have rows : retainedSourceRows scalar (retainedKeyMask retained key mask) = retainedSourceRows scalar retained :=
      retainedSourceRows_fields scalar retained.1 retained.2.1 (key, mask) retained.2.2.1 retained.2.2.2 retained.2.2.2
    unfold retainedProductChoose
    change retainedPrefixChoice adversary parameter auxiliary retained selected _ = _
    rw [rows]
    rfl
  have ghost :
      (∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
          (retainedKeyMask retained key mask) full selected output hidden) =
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden := by
    apply tsum_congr
    intro hidden
    have same : retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
        (retainedKeyMask retained key mask) full selected output hidden =
        retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden := rfl
    exact congrArg ((PMF.uniformOfFintype BaseField) hidden * ·) same
  exact congrArg₂ (HMul.hMul : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) choice ghost
omit [Nonempty BaseField] in
private theorem missTotal_rekey [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (retained : MaskRetainedTape) (key : BaseField) (mask : NonZeroBase) :
    retainedMissTotal adversary parameter auxiliary scalar fallback output
      (retainedKeyMask retained key mask) =
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
        retainedProductMiss adversary parameter auxiliary scalar fallback retained output key mask full selected := by
  unfold retainedMissTotal
  apply tsum_congr
  intro full
  apply congrArg (_ * ·)
  apply tsum_congr
  intro selected
  have choice : retainedPrefixChoice adversary parameter auxiliary
      (retainedKeyMask retained key mask) selected
      (circuitMaskSourceTable (retainedKeyMask retained key mask).2.2.1.1
        (retainedKeyMask retained key mask).2.2.1.2.value
        (retainedSourceRows scalar (retainedKeyMask retained key mask)) (decodeFullSource full)) =
      retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected := by
    have rows : retainedSourceRows scalar (retainedKeyMask retained key mask) = retainedSourceRows scalar retained :=
      retainedSourceRows_fields scalar retained.1 retained.2.1 (key, mask) retained.2.2.1 retained.2.2.2 retained.2.2.2
    unfold retainedProductChoose
    change retainedPrefixChoice adversary parameter auxiliary retained selected _ = _
    rw [rows]
    rfl
  have miss : retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
      (retainedKeyMask retained key mask) full selected output =
      retainedProductMiss adversary parameter auxiliary scalar fallback retained output key mask full selected := rfl
  exact congrArg₂ (HMul.hMul : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞) choice miss

end
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1
private theorem productSamples [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1)
    (keys : PMF BaseField) (masks : PMF NonZeroBase)
    (keysEq : keys = PMF.uniformOfFintype BaseField)
    (masksEq : masks = PMF.uniformOfFintype NonZeroBase) :
    (∑' key, keys key *
      ∑' mask, masks mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
              retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden) ≤
    ∑' key, keys key *
      ∑' mask, masks mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            retainedProductMiss adversary parameter auxiliary scalar fallback retained output key mask full selected := by
  subst keys
  subst masks
  exact retainedGhostProduct_mass_le adversary parameter auxiliary scalar fallback retained output invalid

set_option maxRecDepth 2048 in
private theorem frameBound [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1) (frame : RetainedSourceFrame)
    (keys : PMF BaseField) (masks : PMF NonZeroBase)
    (keysEq : keys = PMF.uniformOfFintype BaseField)
    (masksEq : masks = PMF.uniformOfFintype NonZeroBase) :
    (∑' key, keys key *
      ∑' mask, masks mask *
        retainedGhostTotal adversary parameter auxiliary scalar fallback output
          (retainedFrameEquiv.symm (frame, key, mask))) ≤
    ∑' key, keys key *
      ∑' mask, masks mask *
        retainedMissTotal adversary parameter auxiliary scalar fallback output
          (retainedFrameEquiv.symm (frame, key, mask)) := by
  let retained := retainedFrameEquiv.symm (frame, (0 : BaseField), (⟨1, one_ne_zero⟩ : NonZeroBase))
  have bound := productSamples adversary parameter auxiliary scalar fallback retained output invalid keys masks keysEq masksEq
  have leftEq := weightedEq keys fun key =>
    weightedEq masks fun mask =>
      ghostTotal_rekey adversary parameter auxiliary scalar fallback output retained key mask
  have rightEq := weightedEq keys fun key =>
    weightedEq masks fun mask =>
      missTotal_rekey adversary parameter auxiliary scalar fallback output retained key mask
  have moved := leftEq.trans_le (bound.trans_eq rightEq.symm)
  have frameUpdate (key : BaseField) (mask : NonZeroBase) :
      retainedKeyMask retained key mask = retainedFrameEquiv.symm (frame, key, mask) :=
    retainedFrame_update frame 0 key (⟨1, one_ne_zero⟩ : NonZeroBase) mask
  have leftMove := weightedEq keys fun key =>
    weightedEq masks fun mask =>
      congrArg (retainedGhostTotal adversary parameter auxiliary scalar fallback output)
        (frameUpdate key mask)
  have rightMove := weightedEq keys fun key =>
    weightedEq masks fun mask =>
      congrArg (retainedMissTotal adversary parameter auxiliary scalar fallback output)
        (frameUpdate key mask)
  exact leftMove.symm.trans_le (moved.trans_eq rightMove)

set_option maxRecDepth 2048 in
/-- The frame average keeps the exact normalized invalid source comparison. -/
theorem retainedGhost_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1) :
    (∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained *
      retainedGhostTotal adversary parameter auxiliary scalar fallback output retained) ≤
    ∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained *
      retainedMissTotal adversary parameter auxiliary scalar fallback output retained := by
  apply frameComparison
    (retainedGhostTotal adversary parameter auxiliary scalar fallback output)
    (retainedMissTotal adversary parameter auxiliary scalar fallback output)
  intro frame
  exact frameBound adversary parameter auxiliary scalar fallback output invalid frame
    (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype NonZeroBase) rfl rfl

end
end Kriterion.ArgoMAC.Security
