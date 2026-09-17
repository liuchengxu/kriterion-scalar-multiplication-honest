import Proof.Privacy.Source.Invalid.InvalidGhostFrameSum
import Proof.Privacy.Source.SourceGoodExpansion
namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

private theorem swapTotal {Full Retained : Type*}
    (fulls : PMF Full) (retaineds : PMF Retained)
    (weight : Full → Retained → ℝ≥0∞) (total : Retained → ℝ≥0∞)
    (mass : ℝ≥0∞)
    (massEq : mass = ∑' full, fulls full * ∑' retained, retaineds retained * weight full retained)
    (totalEq : ∀ retained, total retained = ∑' full, fulls full * weight full retained) :
    mass = ∑' retained, retaineds retained * total retained := by
  rw [massEq]
  simp_rw [totalEq, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro retained
  apply tsum_congr
  intro full
  ac_rfl

private theorem sharedSamples [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) (output : FullGateTranscript adversary.State)
    (fulls : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest)) (retaineds : PMF MaskRetainedTape)
    (fullsEq : fulls = PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (retainedsEq : retaineds = PMF.uniformOfFintype MaskRetainedTape) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output =
    ∑' full, fulls full *
      ∑' retained : MaskRetainedTape, retaineds retained *
        ∑' selected,
          (gateSourceChoose adversary parameter auxiliary
            (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
              (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) selected *
          ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
            retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              retained full selected output hidden := by
  subst fulls
  subst retaineds
  exact fullGateGhostGood_mass_shared adversary parameter auxiliary scalar witness fallback output

private theorem totalSamples [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) (retained : MaskRetainedTape)
    (fulls : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (fullsEq : fulls = PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) :
    retainedGhostTotal adversary parameter auxiliary scalar fallback output retained =
    ∑' full, fulls full * ∑' selected,
      (gateSourceChoose adversary parameter auxiliary
        (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
          (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) selected *
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
          retained full selected output hidden := by
  subst fulls
  unfold retainedGhostTotal
  apply tsum_congr
  intro full
  apply congrArg (_ * ·)
  apply tsum_congr
  intro selected
  rfl

set_option maxRecDepth 2048 in
private theorem normalizedSamples [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (fulls : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest)) (retaineds : PMF MaskRetainedTape)
    (fullsEq : fulls = PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (retainedsEq : retaineds = PMF.uniformOfFintype MaskRetainedTape) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output =
    ∑' retained, retaineds retained *
      retainedGhostTotal adversary parameter auxiliary scalar fallback output retained := by
  apply swapTotal fulls retaineds
    (fun full retained => ∑' selected,
      (gateSourceChoose adversary parameter auxiliary
        (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
          (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) selected *
      ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
        retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
          retained full selected output hidden)
    (retainedGhostTotal adversary parameter auxiliary scalar fallback output)
  · exact sharedSamples adversary parameter auxiliary scalar witness fallback output fulls retaineds fullsEq retainedsEq
  · intro retained
    exact totalSamples adversary parameter auxiliary scalar fallback output retained fulls fullsEq

set_option maxRecDepth 2048 in
/-- The good ghost mass equals the exact retained-source average. -/
theorem fullGateGhostGood_mass_retained [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output =
    ∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained *
      retainedGhostTotal adversary parameter auxiliary scalar fallback output retained := by
  exact normalizedSamples adversary parameter auxiliary scalar witness fallback output
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (PMF.uniformOfFintype MaskRetainedTape) rfl rfl

/-- The complete invalid ghost source is bounded by the actual missing-query source. -/
theorem fullGateGhostGood_mass_le_retainedMiss [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (invalid : ¬ OnCurve output.2.1.1) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≤
    ∑' retained, (PMF.uniformOfFintype MaskRetainedTape) retained *
      retainedMissTotal adversary parameter auxiliary scalar fallback output retained := by
  exact (fullGateGhostGood_mass_retained adversary parameter auxiliary scalar witness fallback output).trans_le
    (retainedGhost_mass_le adversary parameter auxiliary scalar fallback output invalid)

end
end Kriterion.ArgoMAC.Security
