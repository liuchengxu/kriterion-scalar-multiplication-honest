import Proof.Privacy.Transcript.SharedIdealGateGame
import Proof.Privacy.Transcript.SharedTranscriptInvariant

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The shared input-choice source retains the exact final prefix state. -/
theorem sharedGateSourceChoose_final {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (member : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary table data).support) :
    selected.2.2.1 = transcriptFinalState idealOracleHandler (sharedInitialSourceOracle data) selected.2.2.2 ∧
      OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) selected.2.2.2 := by
  simp only [sharedGateSourceChoose, PMF.mem_support_map_iff] at member
  obtain ⟨result, supported, rfl⟩ := member
  exact ⟨runTranscript_finalState idealOracleHandler _ _ result supported,
    runOracleProgramWithTranscript_compatible idealOracleHandler _ _ result supported⟩

/-- The shared input-choice source preserves all three public oracle families. -/
theorem sharedGateSourceChoose_oracles {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (member : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary table data).support) :
    selected.2.2.1.fixedOracle = Shared.restrictOracle data.fixedKeyOracle ∧
      selected.2.2.1.encOracle = data.encPRFOracle ∧ selected.2.2.1.hashOracle = data.hashOracle := by
  rw [(sharedGateSourceChoose_final adversary parameter auxiliary table data selected member).1]
  exact sharedIdealTranscriptFinal_oracles (sharedInitialSourceOracle data) selected.2.2.2

/-- The shared continuation keeps its table, input, prefix, and selected labels. -/
theorem sharedGateSourceObserve_tag {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (view : SelectedGateView) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ (sharedGateSourceObserve adversary parameter auxiliary table selected view data).support) :
    (output.1, output.2.1, output.2.2.1, output.2.2.2.1) =
      (table, (selected.1, selected.2.1), selected.2.2.2, sourceInputLabels data selected.1) := by
  simp only [sharedGateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨result, _, rfl⟩ := member
  rfl

/-- The shared selected-view program preserves the encryption and hash functions. -/
theorem sharedProgramSelectedGateView_nonfixed (state : Shared.Simulator.OracleState)
    (input : AffineInput) (mac : InputMac) (view : SelectedGateView) :
    (sharedProgramSelectedGateView state input mac view).encOracle = state.encOracle ∧
      (sharedProgramSelectedGateView state input mac view).hashOracle = state.hashOracle :=
  Shared.Simulator.commands_other state _

/-- A compatible shared transcript has the exact nonfixed public answers. -/
theorem sharedIdealTranscript_nonfixed (state : Shared.Simulator.OracleState)
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (history : List (Sigma sharedRealOracleSpec.Answer))
    (enc : state.encOracle = oracle.2.1) (hash : state.hashOracle = oracle.2.2)
    (compatible : OracleTranscriptCompatible idealOracleHandler state history) :
    SharedNonFixedTranscriptCompatible oracle history := by
  rw [sharedIdealTranscriptCompatible_iff, sharedPublicTranscriptCompatible_iff] at compatible
  rw [enc, hash] at compatible
  exact (sharedNonFixedTranscriptCompatible_fixed state.fixedOracle oracle.1 oracle.2.1 oracle.2.2 history).mp compatible.2

/-- Both shared source phases keep the same nonfixed public answers. -/
theorem sharedGateSourceObserve_nonfixed {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (selectedMember : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary table data).support)
    (view : SelectedGateView) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ (sharedGateSourceObserve adversary parameter auxiliary table selected view data).support) :
    SharedNonFixedTranscriptCompatible
      (Shared.restrictOracle data.fixedKeyOracle, data.encPRFOracle, data.hashOracle)
      (output.2.2.1 ++ output.2.2.2.2.2) := by
  have first := (sharedGateSourceChoose_final adversary parameter auxiliary table data selected selectedMember).2
  have oracles := sharedGateSourceChoose_oracles adversary parameter auxiliary table data selected selectedMember
  simp only [sharedGateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨result, supported, rfl⟩ := member
  apply (sharedNonFixedTranscriptCompatible_append _ _ _).mpr
  constructor
  · exact sharedIdealTranscript_nonfixed (sharedInitialSourceOracle data) _ _ rfl rfl first
  · have same := sharedProgramSelectedGateView_nonfixed selected.2.2.1 selected.1
      (sourceInputLabels data selected.1).inputMac view
    exact sharedIdealTranscript_nonfixed _ _ _ (same.1.trans oracles.2.1) (same.2.trans oracles.2.2)
      (runOracleProgramWithTranscript_compatible idealOracleHandler _ _ result supported)

end
end Kriterion.ArgoMAC.Security
