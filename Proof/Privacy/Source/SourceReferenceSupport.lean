import Proof.Privacy.Source.GhostSourceGood
import Proof.Privacy.Source.SourceTranscriptCompatibility

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- A nonzero good mass has a supported good source and continuation. -/
theorem sourceGoodMass_support {Source Transcript : Type*}
    (samples : PMF Source) (kernel : Source → PMF Transcript) (bad : Set Source) (output : Transcript)
    (nonzero : sourceGoodMass samples kernel bad output ≠ 0) :
    ∃ source, source ∈ samples.support ∧ source ∉ bad ∧ output ∈ (kernel source).support := by
  classical
  by_contra missing
  apply nonzero
  unfold sourceGoodMass
  apply ENNReal.tsum_eq_zero.mpr
  intro source
  by_cases sampleZero : samples source = 0
  · simp [sampleZero]
  by_cases badSource : source ∈ bad
  · simp [badSource]
  have kernelZero : kernel source output = 0 := by
    by_contra supported
    exact missing ⟨source, sampleZero, badSource, supported⟩
  simp [kernelZero]

/-- The supported source phases supply compatible reference states for both transcript segments. -/
theorem gateSourceObserve_references {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (selectedMember : selected ∈ (gateSourceChoose adversary parameter auxiliary table data).support)
    (view : SelectedGateView) (output : FullGateTranscript adversary.State)
    (member : output ∈ (gateSourceObserve adversary parameter auxiliary table selected view data).support) :
    ∃ referenceBefore referenceAfter : SimulatorState,
      OracleTranscriptCompatible idealOracleHandler referenceBefore output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler referenceAfter output.2.2.2.2.2 := by
  simp only [gateSourceChoose, PMF.mem_support_map_iff] at selectedMember
  obtain ⟨first, firstMember, rfl⟩ := selectedMember
  simp only [gateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨last, lastMember, rfl⟩ := member
  exact ⟨initialSourceOracle data, _,
    runOracleProgramWithTranscript_compatible idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) (initialSourceOracle data) first firstMember,
    runOracleProgramWithTranscript_compatible idealOracleHandler
      (adversary.decide parameter table (sourceInputLabels data first.1.1) auxiliary first.1.2)
      (programSelectedGateView first.2.1 first.1.1 (sourceInputLabels data first.1.1).inputMac view)
      last lastMember⟩

/-- A nonzero prefix good mass supplies both compatible reference states. -/
theorem fullGatePrefixGood_references [FieldCertificate] [GroupCertificate] {Aux : Type}
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
    ∃ referenceBefore referenceAfter : SimulatorState,
      OracleTranscriptCompatible idealOracleHandler referenceBefore output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler referenceAfter output.2.2.2.2.2 := by
  classical
  obtain ⟨sample, sampleMember, good, member⟩ := sourceGoodMass_support _ _ _ output nonzero
  have complete : FullSourceComplete sample.2.1.1 := by
    exact not_not.mp (not_or.mp good).1
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at sampleMember
  obtain ⟨randomness, _, tag, _, selected, selectedMember, rfl⟩ := sampleMember
  simp only [fullGatePrefixKernel, complete, if_true] at member
  exact gateSourceObserve_references adversary parameter auxiliary _ _ selected selectedMember _ output member

/-- A nonzero ghost good mass supplies both compatible reference states. -/
theorem fullGateGhostGood_references [FieldCertificate] [GroupCertificate] [Fintype BaseField] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≠ 0) :
    ∃ referenceBefore referenceAfter : SimulatorState,
      OracleTranscriptCompatible idealOracleHandler referenceBefore output.2.2.1 ∧
      OracleTranscriptCompatible idealOracleHandler referenceAfter output.2.2.2.2.2 := by
  apply fullGatePrefixGood_references adversary parameter auxiliary scalar witness fallback output
  intro zero
  apply nonzero
  apply le_antisymm
  · exact (fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar witness fallback output).trans_eq zero
  · exact bot_le

/-- A nonzero prefix good mass obeys the original total query budget. -/
theorem fullGatePrefixGood_length_le [FieldCertificate] [GroupCertificate] {Aux : Type}
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
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  classical
  obtain ⟨sample, sampleMember, good, member⟩ := sourceGoodMass_support _ _ _ output nonzero
  have complete : FullSourceComplete sample.2.1.1 := not_not.mp (not_or.mp good).1
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at sampleMember
  obtain ⟨randomness, _, tag, _, selected, selectedMember, rfl⟩ := sampleMember
  simp only [fullGatePrefixKernel, complete, if_true] at member
  exact gateSourceObserve_length_le adversary parameter auxiliary _ selected _ _
    (gateSourceChoose_length_le adversary parameter auxiliary _ _ selected selectedMember) output member

/-- A nonzero ghost good mass obeys the original total query budget. -/
theorem fullGateGhostGood_length_le [FieldCertificate] [GroupCertificate] [Fintype BaseField] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux) (scalar : ScalarField)
    (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest → PMF (FullGateTranscript adversary.State))
    (output : FullGateTranscript adversary.State)
    (nonzero : sourceGoodMass (fullGateGhostSamples adversary parameter auxiliary scalar witness fallback)
      (fun coin => PMF.pure coin.1.2) {coin | fullGateGhostBad coin} output ≠ 0) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  apply fullGatePrefixGood_length_le adversary parameter auxiliary scalar witness fallback output
  intro zero
  apply nonzero
  apply le_antisymm
  · exact (fullGateGhostGood_le_prefixGood adversary parameter auxiliary scalar witness fallback output).trans_eq zero
  · exact bot_le

end
end Kriterion.ArgoMAC.Security
