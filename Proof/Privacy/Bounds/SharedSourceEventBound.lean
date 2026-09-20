import Proof.Privacy.Source.SharedCombinedRatio
import Proof.Privacy.Transcript.SharedGateEndpoint
import Proof.Shared.SourceHCoefficient

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance 10] Classical.propDecidable
set_option maxRecDepth 4096

private theorem eventFinite {Sample : Type*} (samples : PMF Sample) (event : Set Sample) :
    samples.toOuterMeasure event ≠ ⊤ := by
  rw [PMF.toOuterMeasure_apply]
  exact samples.tsum_coe_indicator_ne_top event

/-- One prefix bound and the exact invalid hash bound control the combined source guard. -/
theorem sharedCombinedBad_real_mass_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (prefixBound : ℝ)
    (prefixMass : ((sharedFullGatePrefixSamples scalar witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {coin | sharedFullPipelinePrefixBad scalar coin}).toReal ≤ prefixBound) :
    ((sharedCombinedSource adversary parameter auxiliary scalar witness fallback).toOuterMeasure
      {coin | sharedCombinedBad scalar coin}).toReal ≤ prefixBound +
      ((278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 +
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus) := by
  have comparison := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨eventFinite _ _, eventFinite _ _⟩)
    (sharedCombinedBad_mass_le adversary parameter auxiliary scalar witness fallback)
  rw [ENNReal.toReal_add (eventFinite _ _) (eventFinite _ _)] at comparison
  exact comparison.trans (add_le_add prefixMass
    (sharedFullInvalidHashHit_mass_le adversary parameter auxiliary scalar witness fallback))

/-- The combined shared source ratio bounds every complete real versus ideal transcript event. -/
theorem sharedAdaptiveTranscript_event_bound [FieldCertificate] [GroupCertificate] [TerminationCertificate]
    [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) (prefixBound : ℝ)
    (prefixMass : ((sharedFullGatePrefixSamples scalar.value witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).toOuterMeasure
        {coin | sharedFullPipelinePrefixBad scalar.value coin}).toReal ≤ prefixBound)
    (small : adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ≤ 2 ^ 101)
    (event : Set (SharedFullGateTranscript adversary.State)) :
    |((realAdaptiveTranscriptWithState sharedInternalCircuit
        (uniformRandomTape Shared.Randomness witness) sharedRealOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal -
      ((idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology Shared.Simulator.simulator
        circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal| ≤
      prefixBound + (54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : ℝ) / 2 ^ 128 +
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus +
      2 * (278638 * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384) + (2 : ℝ) ^ (-240 : ℤ) := by
  have bad := sharedCombinedBad_real_mass_le adversary parameter auxiliary scalar.value witness fallback prefixBound prefixMass
  have ratio := hCoefficient_event_of_sourceGoodMass
    (realAdaptiveTranscriptWithState sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
      sharedRealOracleHandler adversary parameter scalar auxiliary)
    (sharedCombinedSource adversary parameter auxiliary scalar.value witness fallback)
    (fun coin => PMF.pure coin.2) {coin | sharedCombinedBad scalar.value coin}
    (((54691280 + 368 * (adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter) : Nat) : ENNReal) /
      (2 : ENNReal) ^ 128) (by finiteness) _ bad
    (fun output => sharedCombinedGood_real_le adversary parameter auxiliary scalar witness fallback output small) event
  rw [sharedCombinedSource_project] at ratio
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at ratio
  have entrance := actualSharedFullGateSource_idealTranscript_bound adversary parameter scalar auxiliary witness fallback event
  have combined := (abs_sub_le
    ((realAdaptiveTranscriptWithState sharedInternalCircuit (uniformRandomTape Shared.Randomness witness)
      sharedRealOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal
    ((actualSharedFullGateSource scalar.value witness parameter
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback).toOuterMeasure event).toReal
    ((idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology Shared.Simulator.simulator
      circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure event).toReal).trans
      (add_le_add ratio entrance)
  convert combined using 1 <;> push_cast
  all_goals first | rfl | ring

end
end Kriterion.ArgoMAC.Security
