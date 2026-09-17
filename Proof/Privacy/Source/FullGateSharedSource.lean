import Proof.Privacy.Source.FullSourceTape
import Proof.Privacy.Source.FullGateGhostMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable instFintypeRawCircuitGate_1
  instFintypeCircuitMaskTables instFintypeCircuitHashRest_1 instNonemptyCircuitHashRest_1

/-- This kernel keeps the actual tape, source tag, prefix, continuation, and ghost key. -/
def fullGateTapeGhostKernel [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (randomness : Garbling.Randomness) (tag : FullCircuitSource) :=
  let retained := maskRetainedTape randomness
  let full := (tag.1, sharedCircuitHashRest randomness tag.2)
  let table := circuitMaskSourceTable retained.2.2.1.1 retained.2.2.1.2.value
    (retainedSourceRows scalar retained) (decodeFullSource full)
  (gateSourceChoose adversary parameter auxiliary table retained.2.2.2).bind fun selected =>
    let prefixCoin : FullGatePrefixCoin adversary.State := (randomness, tag, selected)
    (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback prefixCoin).bind fun transcript =>
        (PMF.uniformOfFintype BaseField).map fun hiddenKey => ((prefixCoin, transcript), hiddenKey)

set_option maxRecDepth 2048 in
/-- The actual ghost source is the normalized shared-randomizer source. -/
theorem fullGateGhostSamples_shared [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State)) :
    fullGateGhostSamples adversary parameter auxiliary scalar witness fallback =
      (PMF.uniformOfFintype ((RawCircuitGate → FullHashLift) × CircuitHashRest)).bind (fun full =>
        (PMF.uniformOfFintype MaskRetainedTape).bind fun retained =>
          fullGateTapeGhostKernel adversary parameter auxiliary scalar fallback
            (fullSourceTape retained full).1 (fullSourceTape retained full).2) := by
  have law := fullSourceTape_observation_eq witness parameter
    (fullGateTapeGhostKernel adversary parameter auxiliary scalar fallback)
  rw [← law]
  simp only [fullGateGhostSamples, ghostAugment, fullGateTranscriptSamples, fullGatePrefixSamples,
    PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

end
end Kriterion.ArgoMAC.Security
