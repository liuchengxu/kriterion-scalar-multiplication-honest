import Proof.Privacy.Source.Invalid.InvalidGhostSelectedSum
import Proof.Shared.SourceSumComparison

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- This coefficient retains one selected prefix of the actual adaptive choice. -/
def retainedPrefixChoice [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (retained : MaskRetainedTape)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (table : Pipeline.Table) : ℝ≥0∞ :=
  (gateSourceChoose adversary parameter auxiliary table retained.2.2.2) selected

/-- This choice uses the actual adaptive table and every retained oracle function. -/
def retainedProductChoose [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (retained : MaskRetainedTape)
    (key : BaseField) (mask : NonZeroBase) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) : ℝ≥0∞ :=
  retainedPrefixChoice adversary parameter auxiliary retained selected
    (circuitMaskSourceTable key mask.value (retainedSourceRows scalar retained) (decodeFullSource full))

/-- This weight keeps the actual ghost event under the independent key and mask source. -/
def retainedProductGhost [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (output : FullGateTranscript adversary.State)
    (key : BaseField) (mask : NonZeroBase) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (hidden : BaseField) : ℝ≥0∞ :=
  retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
    (retainedKeyMask retained key mask) full selected output hidden

/-- This weight keeps the actual good prescription after the hidden-key restoration. -/
def retainedProductMiss [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (output : FullGateTranscript adversary.State)
    (key : BaseField) (mask : NonZeroBase) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) : ℝ≥0∞ :=
  retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
    (retainedKeyMask retained key mask) full selected output

private theorem selectedSumAbstract [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript adversary.State) (invalid : ¬ OnCurve output.2.1.1)
    (choose : Pipeline.Table → ℝ≥0∞)
    (keys : PMF BaseField) (masks : PMF NonZeroBase)
    (fulls : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (keysEq : keys = PMF.uniformOfFintype BaseField)
    (masksEq : masks = PMF.uniformOfFintype NonZeroBase)
    (fullsEq : fulls = PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) :
    (∑' oldMask : NonZeroBase, masks oldMask *
      ∑' hidden, keys hidden *
        ∑' oldKey, keys oldKey *
          ∑' full, fulls full *
            (choose (circuitMaskSourceTable oldKey oldMask.value (retainedSourceRows scalar retained)
              (decodeFullSource full)) *
              retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
                (retainedKeyMask retained oldKey oldMask) full selected output hidden)) ≤
    ∑' hidden, keys hidden *
      ∑' mask : NonZeroBase, masks mask *
        ∑' full, fulls full *
          (choose (circuitMaskSourceTable hidden mask.value (retainedSourceRows scalar retained)
            (decodeFullSource full)) *
            retainedMissWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              (retainedKeyMask retained hidden mask) full selected output) := by
  subst keys
  subst masks
  subst fulls
  exact retainedGhostWeight_selected_sum_le adversary parameter auxiliary scalar fallback retained selected output invalid choose

set_option maxRecDepth 2048 in
/-- The whole adaptive invalid source restores the real nonzero mask without an additive error. -/
private theorem productAbstract [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1)
    (keys : PMF BaseField) (masks : PMF NonZeroBase)
    (fulls : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (keysEq : keys = PMF.uniformOfFintype BaseField)
    (masksEq : masks = PMF.uniformOfFintype NonZeroBase)
    (fullsEq : fulls = PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) :
    (∑' key, keys key *
      ∑' mask, masks mask *
        ∑' full, fulls full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            ∑' hidden, keys hidden *
              retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden) ≤
    ∑' key, keys key *
      ∑' mask, masks mask *
        ∑' full, fulls full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            retainedProductMiss adversary parameter auxiliary scalar fallback retained output key mask full selected := by
  apply weightedGhost_comparison keys masks fulls keys
    (retainedProductChoose adversary parameter auxiliary scalar retained)
    (retainedProductGhost adversary parameter auxiliary scalar fallback retained output)
    (retainedProductMiss adversary parameter auxiliary scalar fallback retained output)
  intro selected
  unfold retainedProductChoose retainedProductGhost retainedProductMiss
  exact selectedSumAbstract adversary parameter auxiliary scalar fallback retained
    selected output invalid (retainedPrefixChoice adversary parameter auxiliary retained selected)
    keys masks fulls keysEq masksEq fullsEq

set_option maxRecDepth 2048 in
/-- The whole adaptive invalid source restores the real nonzero mask without an additive error. -/
theorem retainedGhostProduct_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1) :
    (∑' key, (PMF.uniformOfFintype BaseField) key *
      ∑' mask, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
              retainedProductGhost adversary parameter auxiliary scalar fallback retained output key mask full selected hidden) ≤
    ∑' key, (PMF.uniformOfFintype BaseField) key *
      ∑' mask, (PMF.uniformOfFintype NonZeroBase) mask *
        ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
          ∑' selected, retainedProductChoose adversary parameter auxiliary scalar retained key mask full selected *
            retainedProductMiss adversary parameter auxiliary scalar fallback retained output key mask full selected := by
  exact productAbstract adversary parameter auxiliary scalar fallback retained output invalid
    (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype NonZeroBase)
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) rfl rfl rfl

end
end Kriterion.ArgoMAC.Security
