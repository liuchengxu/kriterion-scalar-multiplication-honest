import Proof.Privacy.Transcript.SharedTargetGateGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The shared ideal gate source is the actual ideal adaptive transcript. -/
theorem actualSharedIdealGateSource_eq_idealTranscript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    actualSharedIdealGateSourceRun scalar.value
      (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
      (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2) =
      idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology
        Shared.Simulator.simulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary :=
  (actualSharedIdealGateSource_eq_target scalar.value (sharedGateSourceChoose adversary parameter auxiliary)
    (sharedGateSourceObserve adversary parameter auxiliary)).trans
    (sharedTargetGateSourceRun_eq_idealTranscript adversary parameter scalar auxiliary)

/-- The actual shared full source reaches the complete ideal transcript with the checked entrance loss. -/
theorem actualSharedFullGateSource_idealTranscript_bound [FieldCertificate] [GroupCertificate]
    [TerminationCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State))
    (event : Set (SharedFullGateTranscript adversary.State)) :
    |((actualSharedFullGateSource scalar.value witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
        (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback).toOuterMeasure event).toReal -
      ((idealAdaptiveTranscriptWithState sharedInternalCircuit Garbling.topology
        Shared.Simulator.simulator circuitSimulatorOracleHandler adversary parameter scalar auxiliary).toOuterMeasure
          event).toReal| ≤
      (278638 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 + (2 : ℝ) ^ (-240 : ℤ) := by
  rw [← actualSharedIdealGateSource_eq_idealTranscript adversary parameter scalar auxiliary]
  exact actualSharedGateSource_observation_bound scalar.value witness parameter
    (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)
    (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
    fallback event

end
end Kriterion.ArgoMAC.Security
