import Proof.Privacy.Source.Invalid.InvalidGhostSourceTransport
import Proof.Privacy.Source.SourceTranscriptCompatibility

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An incomplete tag contributes no good ghost weight. -/
theorem retainedGhostWeight_incomplete [FieldCertificate] [GroupCertificate] {State : Type}
    (scalar : ScalarField)
    (observe : Pipeline.Table → (AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))) →
      SelectedGateView → GarblingOracleData → PMF (FullGateTranscript State))
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript State) (hidden : BaseField) (incomplete : ¬ FullSourceComplete full.1) :
    retainedGhostWeight scalar observe fallback retained full selected output hidden = 0 := by
  have bad : fullGateGhostBad ((retainedPrefixCoin retained full selected, output), hidden) :=
    Or.inl ((fullGatePrefixBad_reconstructed retained full selected).mpr (Or.inl incomplete))
  exact if_pos bad

/-- A nonzero good ghost weight keeps the chosen input in the actual transcript. -/
theorem retainedGhostWeight_input [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript adversary.State) (hidden : BaseField)
    (nonzero : retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
      retained full selected output hidden ≠ 0) : output.2.1.1 = selected.1 := by
  have complete : FullSourceComplete full.1 := by
    by_contra incomplete
    exact nonzero (retainedGhostWeight_incomplete scalar _ fallback retained full selected output hidden incomplete)
  have member : output ∈ (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback (retainedPrefixCoin retained full selected)).support := by
    apply (PMF.mem_support_iff _ _).mpr
    unfold retainedGhostWeight at nonzero
    split_ifs at nonzero with bad
    · exact False.elim (nonzero rfl)
    · exact nonzero
  rw [retainedPrefixCoin, fullGatePrefixKernel_reconstructed scalar _ fallback retained full selected complete] at member
  have tag := gateSourceObserve_tag adversary parameter auxiliary _ retained.2.2.2 selected _ output member
  exact congrArg (fun value => value.2.1.1) tag

/-- A different selected input contributes no mass to the fixed output transcript. -/
theorem retainedGhostWeight_different_input [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (FullGateTranscript adversary.State))
    (retained : MaskRetainedTape) (full : (RawCircuitGate → FullHashLift) × CircuitHashRest)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (output : FullGateTranscript adversary.State) (hidden : BaseField)
    (different : output.2.1.1 ≠ selected.1) :
    retainedGhostWeight scalar (gateSourceObserve adversary parameter auxiliary) fallback
      retained full selected output hidden = 0 := by
  by_contra nonzero
  exact different (retainedGhostWeight_input adversary parameter auxiliary scalar fallback
    retained full selected output hidden nonzero)

end
end Kriterion.ArgoMAC.Security
