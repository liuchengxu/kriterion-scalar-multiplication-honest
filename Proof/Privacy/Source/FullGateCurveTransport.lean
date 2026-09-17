import Proof.Privacy.Source.FullGateSharedSource

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable

/-- This update keeps the actual row coefficients and oracle data. -/
def retainedKeyMask [FieldCertificate] [GroupCertificate]
    (retained : MaskRetainedTape) (key : BaseField) (mask : NonZeroBase) : MaskRetainedTape :=
  (retained.1, retained.2.1, (key, mask), retained.2.2.2)

/-- The reconstructed prefix kernel reads the exact shared source. -/
theorem fullGatePrefixKernel_reconstructed [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView → SourceOracleRest → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × Prefix) (complete : FullSourceComplete full.1) :
    fullGatePrefixKernel scalar observe fallback
      ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected) =
    observe (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
      (retainedSourceRows scalar retained) (decodeFullSource full)) selected
      (selectedGateView (circuitMaskSampleGarble retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) selected.1 (decodeFullSource full)) selected.1) retained.2.2 := by
  have hash := congrArg Prod.fst (fullSourceTape_source retained full)
  have rest := congrArg Prod.snd (fullSourceTape_source retained full)
  dsimp only at hash rest
  simp only [fullGatePrefixKernel, fullSourceTape_retained, hash, rest, complete, if_true]

/-- The exact complete-source change preserves the continuation seen by the adversary. -/
theorem fullGatePrefixKernel_curveTransport [FieldCertificate] [GroupCertificate] {Prefix Observation : Type*}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × Prefix) → SelectedGateView → GarblingOracleData → PMF Observation)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF Observation)
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × Prefix) (key : BaseField) (mask : NonZeroBase)
    (complete : FullSourceComplete full.1)
    (resultEq : retained.2.2.1.1 + retained.2.2.1.2.value *
        (selected.1.x ^ 3 + 3 - selected.1.y ^ 2) =
      key + mask.value * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2)) :
    let changed := fullCurveMaskEquiv retained.2.2.1.2.value mask.value selected.1 full
    fullGatePrefixKernel scalar (fun table selected view rest => observe table selected view rest.2) fallback
      ((fullSourceTape (retainedKeyMask retained key mask) changed).1,
        (fullSourceTape (retainedKeyMask retained key mask) changed).2, selected) =
    fullGatePrefixKernel scalar (fun table selected view rest => observe table selected view rest.2) fallback
      ((fullSourceTape retained full).1, (fullSourceTape retained full).2, selected) := by
  dsimp only
  have changedComplete := (fullCurveMaskEquiv_complete_iff retained.2.2.1.2.value mask.value selected.1 full).mpr complete
  rw [fullGatePrefixKernel_reconstructed scalar _ fallback _ _ selected changedComplete,
    fullGatePrefixKernel_reconstructed scalar _ fallback retained full selected complete]
  have rows : retainedSourceRows scalar (retainedKeyMask retained key mask) = retainedSourceRows scalar retained :=
    retainedSourceRows_fields scalar retained.1 retained.2.1 (key, mask) retained.2.2.1
      retained.2.2.2 retained.2.2.2
  simp only [retainedKeyMask] at rows ⊢
  rw [rows, fullCurveMaskEquiv_table retained.2.2.1.1 retained.2.2.1.2.value key mask.value
    (retainedSourceRows scalar retained) selected.1 full complete resultEq,
    fullCurveMaskEquiv_garble retained.2.2.1.1 retained.2.2.1.2.value key mask.value
    (retainedSourceRows scalar retained) selected.1 full complete resultEq]

end
end Kriterion.ArgoMAC.Security
