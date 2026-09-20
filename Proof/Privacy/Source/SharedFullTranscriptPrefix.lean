import Proof.Privacy.Source.Invalid.SharedCurveFullSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
set_option maxRecDepth 4096
attribute [local instance 10] Classical.propDecidable
attribute [local instance] bitAdaptorTableFintype instFintypeCircuitMaskTables instFintypeRawCircuitGate_1
attribute [local irreducible] PMF.uniformOfFintype

/-- The full transcript source retains the same tape and tag as the actual adaptive prefix. -/
theorem sharedFullGateTranscriptSamples_prefix [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField) (witness : Shared.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (SharedFullGateTranscript adversary.State)) :
    sharedFullGateTranscriptSamples adversary parameter auxiliary scalar witness fallback =
      (sharedFullGatePrefixSamples scalar witness parameter
        (fun table rest => sharedGateSourceChoose adversary parameter auxiliary table rest.2)).bind fun coin =>
          (sharedFullGatePrefixKernel scalar
            (fun table selected view rest => sharedGateSourceObserve adversary parameter auxiliary table selected view rest.2)
            fallback coin).map fun output => (coin.1, coin.2.1, output) := by
  simp only [sharedFullGateTranscriptSamples, sharedFullGatePrefixSamples, PMF.bind_bind,
    PMF.bind_map, Function.comp_def]
  apply congrArg (uniformRandomTape Shared.Randomness witness parameter).bind
  funext randomness
  apply congrArg₂ PMF.bind
  · apply congrArg (fun finite => @PMF.uniformOfFintype FullCircuitSource finite inferInstance)
    exact Subsingleton.elim _ _
  funext tag
  by_cases complete : FullSourceComplete tag.1
  · simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, fullGateSourceRun,
      complete, if_true, retainedGateSourceRun, PMF.map_bind]
  · simp only [sharedFullGatePrefixKernel, fullGatePrefixKernel, fullGateSourceRun,
      complete, if_false, PMF.bind_const]

end
end Kriterion.ArgoMAC.Security
