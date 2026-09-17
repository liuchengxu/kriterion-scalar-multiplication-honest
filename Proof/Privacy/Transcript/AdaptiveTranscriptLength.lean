import Proof.Privacy.Source.FullGateSourceMass

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- Both adaptive transcripts obey the sum of the two query budgets. -/
theorem sampledTwoPhaseTranscript_length_le {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → PMF (Labels × State))
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : Public × First × List (Sigma oracle.Answer) × Labels × Second × List (Sigma oracle.Answer))
    (member : output ∈ (sampledTwoPhaseTranscript handler samples table state choose encode decide).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤ firstBudget + secondBudget := by
  simp only [sampledTwoPhaseTranscript, twoPhaseTranscript,
    PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨source, _, middle, ⟨first, firstMember, result,
    ⟨encoded, _, last, lastMember, rfl⟩, rfl⟩, rfl⟩ := member
  rw [List.length_append]
  simpa only using Nat.add_le_add (runOracleProgramWithTranscript_length_le _ _ _ first firstMember)
    (runOracleProgramWithTranscript_length_le _ _ _ last lastMember)

/-- The actual real transcript obeys both adversary query budgets. -/
theorem realAdaptiveTranscriptWithState_length_le
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (handler : OracleHandler oracle Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux)
    (output : Public × (Input × adversary.State) × List (Sigma oracle.Answer) ×
      Labels × Bool × List (Sigma oracle.Answer))
    (member : output ∈ (realAdaptiveTranscriptWithState scheme randomTape handler adversary
      parameter circuit auxiliary).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  exact sampledTwoPhaseTranscript_length_le handler (randomTape parameter)
    (fun randomness => (scheme.garble parameter circuit randomness).1) id
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun randomness state selected =>
      PMF.pure (scheme.encode (scheme.garble parameter circuit randomness).2 selected.1, state))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)
    output member

/-- The retained input prefix obeys the first query budget. -/
theorem gateSourceChoose_length_le {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (member : selected ∈ (gateSourceChoose adversary parameter auxiliary table data).support) :
    selected.2.2.2.length ≤ adversary.firstQueryBudget parameter := by
  simp only [gateSourceChoose, PMF.mem_support_map_iff] at member
  obtain ⟨result, member, rfl⟩ := member
  exact runOracleProgramWithTranscript_length_le idealOracleHandler (adversary.chooseInput parameter table auxiliary) (initialSourceOracle data) result member

/-- The source continuation keeps the prefix and obeys the second query budget. -/
theorem gateSourceObserve_length_le {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))
    (view : SelectedGateView) (data : GarblingOracleData)
    (prefixBound : selected.2.2.2.length ≤ adversary.firstQueryBudget parameter)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (gateSourceObserve adversary parameter auxiliary table selected view data).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  simp only [gateSourceObserve, PMF.mem_support_map_iff] at member
  obtain ⟨result, member, rfl⟩ := member
  rw [List.length_append]
  exact Nat.add_le_add prefixBound (runOracleProgramWithTranscript_length_le idealOracleHandler (adversary.decide parameter table (sourceInputLabels data selected.1) auxiliary selected.2.1) (programSelectedGateView selected.2.2.1 selected.1 (sourceInputLabels data selected.1).inputMac view) result member)


/-- Every supported full-source continuation obeys the original total query budget. -/
theorem fullGatePrefixKernel_length_le [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (scalar : ScalarField) (witness : Garbling.Randomness)
    (fallback : MaskRetainedTape → (RawCircuitGate → FullHashLift) × CircuitHashRest →
      PMF (Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
        Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)))
    (fallbackLength : ∀ retained source output, output ∈ (fallback retained source).support →
      (output.2.2.1 ++ output.2.2.2.2.2).length ≤
        adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter)
    (sample : Garbling.Randomness × ((RawCircuitGate → FullHashLift) × CircuitMaskTables) ×
      (AffineInput × (adversary.State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))))
    (sampleMember : sample ∈ (fullGatePrefixSamples scalar witness parameter
      (fun table rest => gateSourceChoose adversary parameter auxiliary table rest.2)).support)
    (output : Pipeline.Table × (AffineInput × adversary.State) × List (Sigma Garbling.oracleSpec.Answer) ×
      Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer))
    (member : output ∈ (fullGatePrefixKernel scalar
      (fun table selected view rest => gateSourceObserve adversary parameter auxiliary table selected view rest.2)
      fallback sample).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  classical
  simp only [fullGatePrefixSamples, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at sampleMember
  obtain ⟨randomness, _, tag, _, selected, selectedMember, rfl⟩ := sampleMember
  by_cases complete : FullSourceComplete tag.1
  · simp only [fullGatePrefixKernel, complete, if_true] at member
    exact gateSourceObserve_length_le adversary parameter auxiliary _ selected _ _
      (gateSourceChoose_length_le adversary parameter auxiliary _ _ selected selectedMember) output member
  · simp only [fullGatePrefixKernel, complete, if_false] at member
    exact fallbackLength _ _ output member

end

end Kriterion.ArgoMAC.Security
