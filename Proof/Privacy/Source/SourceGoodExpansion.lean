import Proof.Privacy.Source.Invalid.InvalidGhostSourceTransport
import Proof.Privacy.Source.SourceGoodMassExpansion

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

set_option maxRecDepth 2048 in
/-- The actual ghost good mass expands into the exact normalized retained-source weights. -/
private theorem fullGateGhostGood_mass_shared_aux [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) (output : FullGateTranscript adversary.State)
    (samples : PMF ((FullGatePrefixCoin adversary.State × FullGateTranscript adversary.State) × BaseField))
    (fullSamples : PMF ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (retainedSamples : PMF MaskRetainedTape) (ghostSamples : PMF BaseField)
    (shared : samples = fullSamples.bind fun full => retainedSamples.bind fun retained =>
      fullGateTapeGhostKernel adversary parameter auxiliary scalar fallback
        (fullSourceTape retained full).1 (fullSourceTape retained full).2)
    (ghostSame : ghostSamples = PMF.uniformOfFintype BaseField) :
    sourceGoodMass samples
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output =
    ∑' full, fullSamples full *
      ∑' retained : MaskRetainedTape, retainedSamples retained *
        ∑' selected,
          (gateSourceChoose adversary parameter auxiliary
            (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
              (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) selected *
          ∑' hidden, ghostSamples hidden *
            retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              retained full selected output hidden := by
  have law := sourceGoodMass_nested_ghost_transport
    (Outer := (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (Inner := MaskRetainedTape)
    (Choice := AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (Source := FullGatePrefixCoin adversary.State) (Ghost := BaseField)
    (Transcript := FullGateTranscript adversary.State)
    samples
    fullSamples
    retainedSamples
    (fun full retained => fullGateTapeGhostKernel adversary parameter auxiliary scalar fallback
      (fullSourceTape retained full).1 (fullSourceTape retained full).2)
    (fun full retained => gateSourceChoose adversary parameter auxiliary
      (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
        (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2)
    (fun full retained selected => retainedPrefixCoin retained full selected)
    (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback)
    ghostSamples (fun coin => fullGateGhostBad coin) output
    (fun full retained selected hidden => retainedGhostWeight scalar
      (gateSourceObserve adversary parameter auxiliary) fallback retained full selected output hidden)
    shared
    (by
      intro full retained
      rw [ghostSame]
      simp only [fullGateTapeGhostKernel, fullSourceTape_retained, fullSourceTape_source]
      rfl)
    (by intro full retained selected hidden; rfl)
  dsimp only [FullGateTranscript] at law ⊢
  exact law

set_option maxRecDepth 2048 in
/-- The actual ghost good mass expands into the exact normalized retained-source weights. -/
theorem fullGateGhostGood_mass_shared [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) (output : FullGateTranscript adversary.State) :
    sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output =
    ∑' full, (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)) full *
      ∑' retained : MaskRetainedTape, (PMF.uniformOfFintype MaskRetainedTape) retained *
        ∑' selected,
          (gateSourceChoose adversary parameter auxiliary
            (circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
              (retainedSourceRows scalar retained) (decodeFullSource full)) retained.2.2.2) selected *
          ∑' hidden, (PMF.uniformOfFintype BaseField) hidden *
            retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
              retained full selected output hidden := by
  exact fullGateGhostGood_mass_shared_aux adversary parameter auxiliary scalar fallback output
    (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
    (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest))
    (PMF.uniformOfFintype MaskRetainedTape) (PMF.uniformOfFintype BaseField)
    (fullGateGhostSamples_shared adversary parameter auxiliary scalar witness fallback) rfl

end
end Kriterion.ArgoMAC.Security
