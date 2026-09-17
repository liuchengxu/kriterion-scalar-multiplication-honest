import Proof.Privacy.Source.SourceReferenceSupport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- A nonzero prefix good mass supplies one reference for the full nonfixed transcript. -/
theorem fullGatePrefixGood_nonfixedReference [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass
      (fullGatePrefixSamples scalar witness parameter
        (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2))
      (fullGatePrefixKernel scalar
        (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
        fallback) {coin | fullGatePrefixBad coin} output ≠ 0) :
    ∃ reference : Garbling.Randomness,
      NonFixedTranscriptCompatible reference (output.2.2.1 ++ output.2.2.2.2.2) := by
  obtain ⟨sample, sampleMember, good, member⟩ := sourceGoodMass_support _ _ _ output nonzero
  have complete : FullSourceComplete sample.2.1.1 := not_not.mp (not_or.mp good).1
  exact ⟨sample.1, fullGatePrefixKernel_nonfixed adversary parameter auxiliary scalar witness
    fallback sample sampleMember complete output member⟩

/-- A nonzero ghost good mass supplies one reference for the full nonfixed transcript. -/
theorem fullGateGhostGood_nonfixedReference [FieldCertificate] [GroupCertificate] [Fintype BaseField] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≠ 0) :
    ∃ reference : Garbling.Randomness,
      NonFixedTranscriptCompatible reference (output.2.2.1 ++ output.2.2.2.2.2) := by
  apply fullGatePrefixGood_nonfixedReference adversary parameter auxiliary scalar witness fallback output
  intro zero
  apply nonzero
  apply le_antisymm
  · exact (fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar witness fallback output).trans_eq zero
  · exact bot_le

end
end Kriterion.ArgoMAC.Security
