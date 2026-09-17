import Proof.Privacy.Source.SourceNonfixedReference
import Proof.Privacy.Source.RealEndpointPhaseMass
import Proof.Privacy.Source.Valid.ValidSourceKernel

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section

/-- The supported good source supplies every shared premise for the two input cases. -/
theorem fullGateGhostGood_sourceFacts [FieldCertificate] [GroupCertificate] [Fintype BaseField] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≠ 0) :
    ∃ referenceBefore referenceAfter : SimulatorState, ∃ nonfixed : Garbling.Randomness, ∃ key : InputMacKey,
      OracleTranscriptCompatible idealOracleHandler referenceBefore output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler referenceAfter output.2.2.2.2.2 ∧
      NonFixedTranscriptCompatible nonfixed (output.2.2.1 ++ output.2.2.2.2.2) ∧
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter ∧
      output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 ∧
      key.encodeAffine output.2.1.1 = output.2.2.2.1.inputMac := by
  obtain ⟨first, last, firstMatch, lastMatch⟩ :=
    fullGateGhostGood_references adversary parameter auxiliary scalar witness fallback output nonzero
  obtain ⟨other, otherMatch⟩ :=
    fullGateGhostGood_nonfixedReference adversary parameter auxiliary scalar witness fallback output nonzero
  refine ⟨first, last, other,
    selectedPublicKey output.2.1.1 (inputMacCoordinateEquiv output.2.2.2.1.inputMac),
    firstMatch, lastMatch, otherMatch,
    fullGateGhostGood_length_le adversary parameter auxiliary scalar witness fallback output nonzero,
    fullGateGhostGood_inputBits adversary parameter auxiliary scalar witness fallback output nonzero, ?_⟩
  rw [selectedPublicKey_encode, Equiv.symm_apply_apply]

end
end Kriterion.ArgoMAC.Security
